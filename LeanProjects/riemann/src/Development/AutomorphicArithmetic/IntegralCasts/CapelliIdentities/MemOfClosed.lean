import Mathlib

theorem UpperTheory.Reformulated.B.Qi13.aux1 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [@IsNonarchimedeanLocalField K inst inst_1 inst_2],
      @IsLocalRing
        (↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
        (@CommSemiring.toSemiring
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@CommRing.toCommSemiring
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))) := by
  intro K _ _ _ _
  infer_instance

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi13.algRes :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [@CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    @Algebra (ZMod l)
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@instIsDomain K (@Field.toSemifield K inst))
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            K inst inst_1 inst_2 inst_3)))
                      (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                      (@DivisionSemiring.toSemiring
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@Semifield.toDivisionSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Field.toSemifield
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@IsLocalRing.ResidueField.field
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))))) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @ZMod.algebra
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionRing.toRing
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Field.toDivisionRing
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@IsLocalRing.ResidueField.field
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))
        l inst_5

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi13.fdim :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [Fact (Nat.Prime l)] →
                  [@CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    Nat :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @Module.finrank (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5))

theorem UpperTheory.Reformulated.B.Qi13.aux4 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l],
      @Module.Free (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@CommSemiring.toSemiring (ZMod l) (@CommRing.toCommSemiring (ZMod l) (ZMod.commRing l)))
        (@AddCommGroup.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Ring.toAddCommGroup
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@DivisionRing.toRing
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toDivisionRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) := by
  intro K _ _ _ _ l _ _
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  exact Module.Free.of_divisionRing (ZMod l) _

theorem UpperTheory.Reformulated.B.Qi13.aux5 :
    ∀ (l : Nat) [Fact (Nat.Prime l)],
      @StrongRankCondition (ZMod l)
        (@CommSemiring.toSemiring (ZMod l) (@CommRing.toCommSemiring (ZMod l) (ZMod.commRing l))) := by
  intro l _
  infer_instance

theorem UpperTheory.Reformulated.B.Qi13.aux6 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l],
      @Module.Finite (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) := by
  intro K _ _ _ _ l _ _
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  haveI : Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := inferInstance
  exact Module.Finite.of_finite

noncomputable def UpperTheory.Reformulated.B.Qi13.bb :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [inst_5 :
                      @CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    @Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@instIsDomain K (@Field.toSemifield K inst))
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            K inst inst_1 inst_2 inst_3)))
                      (@DivisionSemiring.toSemiring (ZMod l)
                        (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                      (@Semiring.toAddCommMonoid
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@DivisionSemiring.toSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Semifield.toDivisionSemiring
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@Field.toSemifield
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@IsLocalRing.ResidueField.field
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))))))
                      (@Algebra.toModule (ZMod l)
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                        (@DivisionSemiring.toSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Semifield.toDivisionSemiring
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@Field.toSemifield
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@IsLocalRing.ResidueField.field
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3))))))
                        (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @Module.finBasis (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
        (@UpperTheory.Reformulated.B.Qi13.aux4 K inst inst_1 inst_2 inst_3 l inst_4 inst_5) (@UpperTheory.Reformulated.B.Qi13.aux5 l inst_4)
        (@UpperTheory.Reformulated.B.Qi13.aux6 K inst inst_1 inst_2 inst_3 l inst_4 inst_5)

theorem UpperTheory.Reformulated.B.Qi13.aux8 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l]
      (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)),
      ∃ (a :
        ↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))),
        @Eq
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DFunLike.coe
            (@RingHom
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Semiring.toNonAssocSemiring
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@CommSemiring.toSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommRing.toCommSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
              (@Semiring.toNonAssocSemiring
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (fun
                (x :
                  ↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
              @IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@RingHom.instFunLike
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Semiring.toNonAssocSemiring
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@CommSemiring.toSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommRing.toCommSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
              (@Semiring.toNonAssocSemiring
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
            (@IsLocalRing.residue
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            a)
          (@DFunLike.coe
            (@Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionSemiring.toSemiring (ZMod l)
                (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
              (@Semiring.toAddCommMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
              (@Algebra.toModule (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
            (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
            (fun (x : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
              @IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Module.Basis.instFunLike (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionSemiring.toSemiring (ZMod l)
                (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
              (@Semiring.toAddCommMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
              (@Algebra.toModule (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
            (@UpperTheory.Reformulated.B.Qi13.bb K inst inst_1 inst_2 inst_3 l inst_4 inst_5) i) := by
  intro K _ _ _ _ l _ _ i
  exact IsLocalRing.residue_surjective _

noncomputable def UpperTheory.Reformulated.B.Qi13.blift :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [inst_5 :
                      @CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5) →
                      ↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l]
        (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
      @Exists.choose
        (↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
        (fun
            (a :
              ↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
          @Eq
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@DFunLike.coe
              (@RingHom
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semiring.toNonAssocSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommSemiring.toSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@CommRing.toCommSemiring
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
                (@Semiring.toNonAssocSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (fun
                  (x :
                    ↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
                @IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@RingHom.instFunLike
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semiring.toNonAssocSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommSemiring.toSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@CommRing.toCommSemiring
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
                (@Semiring.toNonAssocSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
              (@IsLocalRing.residue
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              a)
            (@DFunLike.coe
              (@Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring (ZMod l)
                  (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                (@Semiring.toAddCommMonoid
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
                (@Algebra.toModule (ZMod l)
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                  (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
              (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
              (fun (x : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
                @IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Module.Basis.instFunLike (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring (ZMod l)
                  (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                (@Semiring.toAddCommMonoid
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
                (@Algebra.toModule (ZMod l)
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                  (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
              (@UpperTheory.Reformulated.B.Qi13.bb K inst inst_1 inst_2 inst_3 l inst_4 inst_5) i))
        (@UpperTheory.Reformulated.B.Qi13.aux8 K inst inst_1 inst_2 inst_3 l inst_4 inst_5 i)

private theorem UpperTheory.Reformulated.B.Qi13.key {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    (O : Subring K) {k : Type} [CommRing k] [Algebra (ZMod l) k] (r : O →+* k)
    (hO : ∀ c : ℤ_[l], algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) {ι : Type} [Fintype ι] (x : ι → O)
    (h : LinearIndependent (ZMod l) (fun i => r (x i))) :
    LinearIndependent ℚ_[l] (fun i => (x i : K)) := by
  classical
  let φ : ℤ_[l] →+* O :=
    ((algebraMap ℚ_[l] K).comp PadicInt.Coe.ringHom).codRestrict O hO
  have hφ : ∀ c : ℤ_[l], r (φ c) = algebraMap (ZMod l) k (PadicInt.toZMod c) := by
    intro c
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZMod c)
    have hker : c - (n : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[l] →+* ZMod l) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hn, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
    obtain ⟨d, hd⟩ := hker
    have hl : (l : k) = 0 := by
      rw [← map_natCast (algebraMap (ZMod l) k), ZMod.natCast_self, map_zero]
    have hc : c = n + l * d := by rw [← hd]; ring
    rw [← hn, hc]
    simp only [map_add, map_mul, map_natCast, hl, zero_mul, add_zero]
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  by_contra hne
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hne
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ (fun i => ‖g i‖) ⟨i₀, Finset.mem_univ _⟩
  have hpos : 0 < ‖g m‖ := (norm_pos_iff.mpr hi₀).trans_le (hm i₀ (Finset.mem_univ _))
  have hgm : g m ≠ 0 := norm_pos_iff.mp hpos
  let c : ι → ℤ_[l] := fun i => ⟨g i / g m, by
    rw [norm_div]
    exact (div_le_one hpos).mpr (hm i (Finset.mem_univ _))⟩
  have hsum : ∑ i, φ (c i) * x i = 0 := by
    apply Subtype.ext
    have h1 : ∀ i, ((φ (c i) * x i : O) : K) = (g m)⁻¹ • (g i • (x i : K)) := by
      intro i
      change algebraMap ℚ_[l] K (g i / g m) * (x i : K) = _
      rw [smul_smul, Algebra.smul_def, div_eq_inv_mul]
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [h1]
    rw [← Finset.smul_sum, hg, smul_zero]
    rfl
  have hred : ∑ i, PadicInt.toZMod (c i) • r (x i) = 0 := by
    have h2 := congrArg r hsum
    rw [map_sum, map_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hφ, Algebra.smul_def]
  have h3 := h _ hred m
  have h4 : c m = 1 := Subtype.ext (div_self hgm)
  rw [h4, map_one] at h3
  exact one_ne_zero h3

private theorem UpperTheory.Reformulated.B.Qi13.mem_of_closed {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [TopologicalSpace K] [Algebra ℚ_[l] K] (O : Subring K) (hO : IsClosed (O : Set K))
    (hc : Continuous (algebraMap ℚ_[l] K)) (c : ℤ_[l]) :
    algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O := by
  refine PadicInt.denseRange_natCast.induction_on
    (p := fun c : ℤ_[l] => algebraMap ℚ_[l] K (c : ℚ_[l]) ∈ O) c ?_ ?_
  · exact hO.preimage (hc.comp continuous_subtype_val)
  · intro n
    rw [PadicInt.coe_natCast, map_natCast]
    exact natCast_mem O n

theorem UpperTheory.Reformulated.B.Qi13.linIndep :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @Algebra (@Padic l inst_4) K
          (@Semifield.toCommSemiring (@Padic l inst_4) (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_6 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@IsDiscreteValuationRing.toIsLocalRing
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@instIsDomain K (@Field.toSemifield K inst))
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation K
                inst inst_1 inst_2 inst_3)))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsDiscreteValuationRing.toIsLocalRing
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@instIsDomain K (@Field.toSemifield K inst))
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                  K inst inst_1 inst_2 inst_3)))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsDiscreteValuationRing.toIsLocalRing
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@instIsDomain K (@Field.toSemifield K inst))
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                    K inst inst_1 inst_2 inst_3)))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@IsDiscreteValuationRing.toIsLocalRing
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@instIsDomain K (@Field.toSemifield K inst))
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                      K inst inst_1 inst_2 inst_3)))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@instIsDomain K (@Field.toSemifield K inst))
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        K inst inst_1 inst_2 inst_3)))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@IsDiscreteValuationRing.toIsLocalRing
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@instIsDomain K (@Field.toSemifield K inst))
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                        K inst inst_1 inst_2 inst_3)))))))
          l],
      @Continuous (@Padic l inst_4) K
          (@UniformSpace.toTopologicalSpace (@Padic l inst_4)
            (@PseudoMetricSpace.toUniformSpace (@Padic l inst_4)
              (@SeminormedRing.toPseudoMetricSpace (@Padic l inst_4)
                (@SeminormedCommRing.toSeminormedRing (@Padic l inst_4)
                  (@NormedCommRing.toSeminormedCommRing (@Padic l inst_4)
                    (@NormedField.toNormedCommRing (@Padic l inst_4) (@Padic.normedField l inst_4)))))))
          inst_2
          (@DFunLike.coe
            (@RingHom (@Padic l inst_4) K
              (@Semiring.toNonAssocSemiring (@Padic l inst_4)
                (@CommSemiring.toSemiring (@Padic l inst_4)
                  (@Semifield.toCommSemiring (@Padic l inst_4)
                    (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))))
              (@Semiring.toNonAssocSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Padic l inst_4) (fun (x : @Padic l inst_4) ↦ K)
            (@RingHom.instFunLike (@Padic l inst_4) K
              (@Semiring.toNonAssocSemiring (@Padic l inst_4)
                (@CommSemiring.toSemiring (@Padic l inst_4)
                  (@Semifield.toCommSemiring (@Padic l inst_4)
                    (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))))
              (@Semiring.toNonAssocSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Algebra.algebraMap (@Padic l inst_4) K
              (@Semifield.toCommSemiring (@Padic l inst_4)
                (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) inst_5)) →
        @LinearIndependent (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_6)) (@Padic l inst_4) K
          (fun (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_6)) ↦
            @Subtype.val K
              (fun (x : K) ↦
                @Membership.mem K
                  (@Subring K (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                  (@SetLike.instMembership
                    (@Subring K (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))) K
                    (@Subring.instSetLike K
                      (@Ring.toNonAssocRing K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))))
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))
                  x)
              (@UpperTheory.Reformulated.B.Qi13.blift K inst inst_1 inst_2 inst_3 l inst_4 inst_6 i))
          (@DivisionSemiring.toSemiring (@Padic l inst_4)
            (@Semifield.toDivisionSemiring (@Padic l inst_4)
              (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@Padic l inst_4) K
            (@Semifield.toCommSemiring (@Padic l inst_4) (@Field.toSemifield (@Padic l inst_4) (@instFieldPadic l inst_4)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) inst_5) := by
  intro K _ _ _ _ l _ _ _ hc
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  refine UpperTheory.Reformulated.B.Qi13.key (ValuativeRel.valuation K).integer
    (IsLocalRing.residue (ValuativeRel.valuation K).integer)
    (UpperTheory.Reformulated.B.Qi13.mem_of_closed _ Valuation.isClosed_integer hc)
    (UpperTheory.Reformulated.B.Qi13.blift K l) ?_
  have h : (fun i => IsLocalRing.residue (ValuativeRel.valuation K).integer
      (UpperTheory.Reformulated.B.Qi13.blift K l i)) = UpperTheory.Reformulated.B.Qi13.bb K l :=
    funext fun i => (UpperTheory.Reformulated.B.Qi13.aux8 K l i).choose_spec
  rw [h]
  exact (UpperTheory.Reformulated.B.Qi13.bb K l).linearIndependent
