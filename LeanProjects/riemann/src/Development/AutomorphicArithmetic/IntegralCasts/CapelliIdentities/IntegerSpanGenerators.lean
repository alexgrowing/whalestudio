import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiltrationExponentBound
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DivisibilityFiltration

noncomputable def UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan :
    {G : Type} →
      [inst : Group G] →
        [inst_1 : TopologicalSpace G] →
          {Qp K₀ K : Type} →
            [inst_2 : Field Qp] →
              [inst_3 : Field K₀] →
                [inst_4 : Field K] →
                  [inst_5 :
                      @Algebra Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                        (@DivisionSemiring.toSemiring K₀
                          (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))] →
                    [inst_6 :
                        @Algebra Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                          (@DivisionSemiring.toSemiring K
                            (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))] →
                      [inst_7 :
                          @Algebra K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                            (@DivisionSemiring.toSemiring K
                              (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))] →
                        [inst_8 :
                            @IsScalarTower Qp K₀ K
                              (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                (@DivisionSemiring.toSemiring K₀
                                  (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))
                                inst_5)
                              (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))
                                inst_7)
                              (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))
                                inst_6)] →
                          {B BdR : Type} →
                            [inst_9 : CommRing B] →
                              [inst_10 : CommRing BdR] →
                                [inst_11 :
                                    @Algebra Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                      (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))] →
                                  [inst_12 :
                                      @Algebra K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                        (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))] →
                                    [inst_13 :
                                        @IsScalarTower Qp K₀ B
                                          (@Algebra.toSMul Qp K₀
                                            (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                            (@DivisionSemiring.toSemiring K₀
                                              (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))
                                            inst_5)
                                          (@Algebra.toSMul K₀ B
                                            (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_12)
                                          (@Algebra.toSMul Qp B
                                            (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_11)] →
                                      [inst_14 :
                                          @Algebra Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))] →
                                        [inst_15 :
                                            @Algebra K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))] →
                                          [inst_16 :
                                              @Algebra K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
                                                (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))] →
                                            [inst_17 :
                                                @IsScalarTower Qp K BdR
                                                  (@Algebra.toSMul Qp K
                                                    (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                                    (@DivisionSemiring.toSemiring K
                                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))
                                                    inst_6)
                                                  (@Algebra.toSMul K BdR
                                                    (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
                                                    (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))
                                                    inst_16)
                                                  (@Algebra.toSMul Qp BdR
                                                    (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                                    (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))
                                                    inst_14)] →
                                              [inst_18 :
                                                  @IsScalarTower K₀ K BdR
                                                    (@Algebra.toSMul K₀ K
                                                      (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                                      (@DivisionSemiring.toSemiring K
                                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))
                                                      inst_7)
                                                    (@Algebra.toSMul K BdR
                                                      (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
                                                      (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))
                                                      inst_16)
                                                    (@Algebra.toSMul K₀ BdR
                                                      (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                                      (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))
                                                      inst_15)] →
                                                [inst_19 :
                                                    @IsScalarTower Qp K₀ BdR
                                                      (@Algebra.toSMul Qp K₀
                                                        (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                                        (@DivisionSemiring.toSemiring K₀
                                                          (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))
                                                        inst_5)
                                                      (@Algebra.toSMul K₀ BdR
                                                        (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
                                                        (@CommSemiring.toSemiring BdR
                                                          (@CommRing.toCommSemiring BdR inst_10))
                                                        inst_15)
                                                      (@Algebra.toSMul Qp BdR
                                                        (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                                        (@CommSemiring.toSemiring BdR
                                                          (@CommRing.toCommSemiring BdR inst_10))
                                                        inst_14)] →
                                                  {PD :
                                                      @Formalism.WeaklyAdmissibleFiltrations.PeriodData G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                        inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                        inst_15 inst_16 inst_17 inst_18 inst_19} →
                                                    {LL O : Type} →
                                                      [inst_20 : Field LL] →
                                                        [inst_21 :
                                                            @Algebra Qp LL
                                                              (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
                                                              (@DivisionSemiring.toSemiring LL
                                                                (@Semifield.toDivisionSemiring LL
                                                                  (@Field.toSemifield LL inst_20)))] →
                                                          [inst_22 : TopologicalSpace LL] →
                                                            [inst_23 : CommRing O] →
                                                              [inst_24 :
                                                                  @Algebra O LL (@CommRing.toCommSemiring O inst_23)
                                                                    (@DivisionSemiring.toSemiring LL
                                                                      (@Semifield.toDivisionSemiring LL
                                                                        (@Field.toSemifield LL inst_20)))] →
                                                                {v :
                                                                    @AddValuation LL
                                                                      (@DivisionRing.toRing LL
                                                                        (@Field.toDivisionRing LL inst_20))
                                                                      (WithTop Rat)
                                                                      (@WithTop.linearOrderedAddCommMonoidWithTop Rat
                                                                        (@AddCommGroup.toAddCancelCommMonoid Rat
                                                                          Rat.addCommGroup)
                                                                        Rat.linearOrder Rat.instIsOrderedAddMonoid)} →
                                                                  {n : Nat} →
                                                                    (W :
                                                                        @Formalism.BasicNotions.LocWach G inst inst_1 Qp K₀ K inst_2
                                                                          inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                                                                          inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                                          inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n) →
                                                                      (T :
                                                                          @Formalism.BasicNotions.LocLat G inst inst_1 Qp LL O inst_2
                                                                            inst_20 inst_21 inst_23 inst_24 inst_22) →
                                                                        ZMod n →
                                                                          Nat →
                                                                            Nat →
                                                                              Nat →
                                                                                Nat →
                                                                                  @Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                                                                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp
                                                                                      K₀ K inst_2 inst_3 inst_4 inst_5
                                                                                      inst_6 inst_7 inst_8 B BdR inst_9
                                                                                      inst_10 inst_11 inst_12 inst_13
                                                                                      inst_14 inst_15 inst_16 inst_17
                                                                                      inst_18 inst_19 PD LL O inst_20
                                                                                      inst_21 inst_23 inst_24 inst_22 v n W
                                                                                      T)
                                                                                    (@Pi.semiring (ZMod n)
                                                                                      (fun (a : ZMod n) ↦ PowerSeries O)
                                                                                      fun (i : ZMod n) ↦
                                                                                      @MvPowerSeries.instSemiring Unit O
                                                                                        (@CommSemiring.toSemiring O
                                                                                          (@CommRing.toCommSemiring O
                                                                                            inst_23)))
                                                                                    (@AddCommGroup.toAddCommMonoid
                                                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp
                                                                                        K₀ K inst_2 inst_3 inst_4 inst_5
                                                                                        inst_6 inst_7 inst_8 B BdR inst_9
                                                                                        inst_10 inst_11 inst_12 inst_13
                                                                                        inst_14 inst_15 inst_16 inst_17
                                                                                        inst_18 inst_19 PD LL O inst_20
                                                                                        inst_21 inst_23 inst_24 inst_22 v n
                                                                                        W T)
                                                                                      (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1
                                                                                        Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                                                        inst_6 inst_7 inst_8 B BdR inst_9
                                                                                        inst_10 inst_11 inst_12 inst_13
                                                                                        inst_14 inst_15 inst_16 inst_17
                                                                                        inst_18 inst_19 PD LL O inst_20
                                                                                        inst_21 inst_23 inst_24 inst_22 v n
                                                                                        W T))
                                                                                    (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1
                                                                                      Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                                                      inst_6 inst_7 inst_8 B BdR inst_9
                                                                                      inst_10 inst_11 inst_12 inst_13
                                                                                      inst_14 inst_15 inst_16 inst_17
                                                                                      inst_18 inst_19 PD LL O inst_20
                                                                                      inst_21 inst_23 inst_24 inst_22 v n W
                                                                                      T) :=
    fun {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {Qp K₀ K : Type} [inst_2 : Field Qp] [inst_3 : Field K₀]
        [inst_4 : Field K]
        [inst_5 :
          @Algebra Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))]
        [inst_6 :
          @Algebra Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))]
        [inst_7 :
          @Algebra K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))]
        [inst_8 :
          @IsScalarTower Qp K₀ K
            (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
            (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_7)
            (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_6)]
        {B BdR : Type} [inst_9 : CommRing B] [inst_10 : CommRing BdR]
        [inst_11 :
          @Algebra Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))]
        [inst_12 :
          @Algebra K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))]
        [inst_13 :
          @IsScalarTower Qp K₀ B
            (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
            (@Algebra.toSMul K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_12)
            (@Algebra.toSMul Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_11)]
        [inst_14 :
          @Algebra Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
        [inst_15 :
          @Algebra K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
        [inst_16 :
          @Algebra K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
        [inst_17 :
          @IsScalarTower Qp K BdR
            (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_6)
            (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_16)
            (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_14)]
        [inst_18 :
          @IsScalarTower K₀ K BdR
            (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_7)
            (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_16)
            (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_15)]
        [inst_19 :
          @IsScalarTower Qp K₀ BdR
            (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
            (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_15)
            (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
              (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_14)]
        {PD :
          @Formalism.WeaklyAdmissibleFiltrations.PeriodData G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
            inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19}
        {LL O : Type} [inst_20 : Field LL]
        [inst_21 :
          @Algebra Qp LL (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))]
        [inst_22 : TopologicalSpace LL] [inst_23 : CommRing O]
        [inst_24 :
          @Algebra O LL (@CommRing.toCommSemiring O inst_23)
            (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))]
        {v :
          @AddValuation LL (@DivisionRing.toRing LL (@Field.toDivisionRing LL inst_20)) (WithTop Rat)
            (@WithTop.linearOrderedAddCommMonoidWithTop Rat (@AddCommGroup.toAddCancelCommMonoid Rat Rat.addCommGroup)
              Rat.linearOrder Rat.instIsOrderedAddMonoid)}
        {n : Nat}
        (W :
          @Formalism.BasicNotions.LocWach G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
            inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
            inst_22 v n)
        (T : @Formalism.BasicNotions.LocLat G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22) (i : ZMod n)
        (j M X σ : Nat) ↦
      @Submodule.span (@Formalism.BasicNotions.LetA O inst_23 n)
        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
          inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
          inst_22 v n W T)
        (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
          @MvPowerSeries.instSemiring Unit O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
        (@AddCommGroup.toAddCommMonoid
          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
            inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
            inst_22 v n W T)
          (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
            inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
            inst_24 inst_22 v n W T))
        (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
          inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
          inst_24 inst_22 v n W T)
        (@Set.ofPred
          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
            inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
            inst_22 v n W T)
          fun
            (z :
              @Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                inst_23 inst_24 inst_22 v n W T) ↦
          ∃ (w :
            @Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
              inst_24 inst_22 v n W T),
            And
              (@Membership.mem
                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                  inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                  inst_23 inst_24 inst_22 v n W T)
                (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                    inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                    inst_23 inst_24 inst_22 v n W T)
                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                    @MvPowerSeries.instSemiring Unit O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                  (@AddCommGroup.toAddCommMonoid
                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T)
                    (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T))
                  (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                    inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                    inst_21 inst_23 inst_24 inst_22 v n W T))
                (@SetLike.instMembership
                  (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T)
                    (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                      @MvPowerSeries.instSemiring Unit O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                    (@AddCommGroup.toAddCommMonoid
                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                        inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                      (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                        inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T))
                    (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T))
                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                    inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                    inst_23 inst_24 inst_22 v n W T)
                  (@Submodule.setLike (@Formalism.BasicNotions.LetA O inst_23 n)
                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T)
                    (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                      @MvPowerSeries.instSemiring Unit O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                    (@AddCommGroup.toAddCommMonoid
                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                        inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                      (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                        inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T))
                    (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR
                      inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                      inst_21 inst_23 inst_24 inst_22 v n W T)))
                (@Formalism.BasicNotions.LocWach.N G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                  inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                  inst_23 inst_24 inst_22 v n W T)
                w)
              (And
                (@Formalism.MainNotions.CrystallineLiftingInputs.InI G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                  inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                  inst_22 inst_23 inst_24 v n W T i w)
                (@Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                  inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                  inst_22 inst_23 inst_24 v n W T i j M X σ w z)))

section SlopeTestRemainingChoices

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.CrystallineLiftingInputs Formalism.MainNotions.LiftingTheory

private theorem unit_of_val {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    (v : AddValuation LL (WithTop ℚ)) (hinj : Function.Injective (algebraMap O LL))
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (x y : O) (k : ℕ)
    (hx : v (algebraMap O LL x) = (k : WithTop ℚ)) (hy : v (algebraMap O LL y) = (k : WithTop ℚ)) :
    ∃ u : Oˣ, x = (u : O) * y := by
  have hk : (k : WithTop ℚ) ≠ ⊤ := WithTop.natCast_ne_top k
  have key : ∀ a b : O, v (algebraMap O LL a) = (k : WithTop ℚ) →
      v (algebraMap O LL b) = (k : WithTop ℚ) → b ≠ 0 ∧ ∃ o : O, a = o * b := by
    intro a b ha hb
    have hb0 : algebraMap O LL b ≠ 0 := by
      intro h
      rw [h, v.map_zero] at hb
      exact hk hb.symm
    have h1 : algebraMap O LL a = algebraMap O LL a / algebraMap O LL b * algebraMap O LL b :=
      (div_mul_cancel₀ _ hb0).symm
    have h2 : v (algebraMap O LL a / algebraMap O LL b) = 0 := by
      have h3 := congrArg v h1
      rw [v.map_mul, ha, hb] at h3
      exact (WithTop.add_right_cancel hk ((zero_add _).trans h3)).symm
    obtain ⟨o, ho⟩ := hO _ h2.ge
    refine ⟨fun h => hb0 (by rw [h, map_zero]), o, hinj ?_⟩
    rw [map_mul, ho]
    exact h1
  obtain ⟨hy0, o, ho⟩ := key x y hx hy
  obtain ⟨-, o', ho'⟩ := key y x hy hx
  have h1 : o * o' = 1 := by
    apply hinj
    have hy1 : algebraMap O LL y ≠ 0 := fun h => hy0 (hinj (by rw [h, map_zero]))
    apply mul_right_cancel₀ hy1
    rw [← map_mul, map_one, one_mul]
    congr 1
    calc o * o' * y = o' * (o * y) := by ring
      _ = y := by rw [← ho, ← ho']
  exact ⟨Units.mkOfMulEqOne o o' h1, ho⟩

private theorem val_succ (p : ℕ) (hp : p.Prime) (r : ℕ) :
    (r + 1) + padicValNat p (r + 1).factorial =
      (r + padicValNat p r.factorial) + (1 + padicValNat p (r + 1)) := by
  have := Fact.mk hp
  rw [Nat.factorial_succ, padicValNat.mul (Nat.add_one_ne_zero r) (Nat.factorial_ne_zero r)]
  omega

private theorem val_add (p : ℕ) (hp : p.Prime) (a b : ℕ) :
    (a + padicValNat p a.factorial) + (b + padicValNat p b.factorial) ≤
      (a + b) + padicValNat p (a + b).factorial := by
  have := Fact.mk hp
  have h := Nat.add_choose_mul_factorial_mul_factorial a b
  have h0 : (a + b).choose b ≠ 0 := (Nat.choose_pos (Nat.le_add_left b a)).ne'
  rw [← h, padicValNat.mul (mul_ne_zero h0 (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero b),
    padicValNat.mul h0 (Nat.factorial_ne_zero a)]
  omega

private theorem eY_mono (p : ℕ) (hp : p.Prime) : Monotone (eY p) := by
  intro a b hab
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h3 : (a : ℝ) ≤ b := by exact_mod_cast hab
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by linarith)
  exact mul_le_mul_of_nonneg_right h3 (by linarith)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

private noncomputable def N0 (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    Submodule O (W.DD T) :=
  W.NΔ T ⊓ (W.Nl T i).restrictScalars O

private theorem mem_wachFiltration_iff (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    x ∈ N0 W T i ↔ x ∈ W.N T ∧ DL W T i x := by
  constructor
  · rintro ⟨⟨h1, h2⟩, y, -, hy⟩
    refine ⟨h1, ?_, h2⟩
    have hy' : (letE i : LetA O n) • y = x := hy
    have he : (letE i : LetA O n) * letE i = letE i := by
      funext k
      by_cases h : k = i <;> simp [letE, Pi.single_apply, h]
    rw [← hy', smul_smul, he]
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, x, h1, h2⟩

private theorem smul_mem_wachFiltration (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n)
    (a : LetA O n) (ha : a ∈ W.AΔ) (x : W.DD T) (hx : x ∈ N0 W T i) : a • x ∈ N0 W T i := by
  refine ⟨⟨(W.N T).smul_mem a hx.1.1, fun δ hδ => ?_⟩, (W.Nl T i).smul_mem a hx.2⟩
  have h := W.γD_smul T δ (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul, hx.1.2 δ hδ] at h
  rw [h]
  exact congrArg (· • x) (ha δ hδ)

private theorem sat (W : LocWach PD LL O v n) [IsDomain O] (f : LetA O n)
    (hf : IsUnit (algebraMap (LetA O n) W.EE f)) (a : LetA O n)
    (h : f ∣ ((PD.p : ℕ) : LetA O n) * a) : f ∣ a := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨u, hu⟩ := hf
  have hl : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : ((PD.p : ℕ) : LL) = 0 := by rw [← map_natCast (algebraMap O LL), h0, map_zero]
    have h2 := W.v_l
    rw [h1, v.map_zero] at h2
    exact WithTop.one_ne_top h2.symm
  have hl' : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h0
    apply hl
    have := congrArg PowerSeries.constantCoeff h0
    rwa [map_natCast, map_zero] at this
  obtain ⟨b, hb⟩ := W.EE_sat g 1 (by
    rw [Ideal.mem_span_singleton', pow_one]
    refine ⟨algebraMap (LetA O n) W.EE a * (u⁻¹ : W.EEˣ), ?_⟩
    have h1 := congrArg (algebraMap (LetA O n) W.EE) hg
    rw [map_mul, map_mul, map_natCast, ← hu] at h1
    calc algebraMap (LetA O n) W.EE a * (u⁻¹ : W.EEˣ) * ((PD.p : ℕ) : W.EE)
        = (u⁻¹ : W.EEˣ) * (((PD.p : ℕ) : W.EE) * algebraMap (LetA O n) W.EE a) := by ring
      _ = algebraMap (LetA O n) W.EE g := by rw [h1, Units.inv_mul_cancel_left])
  refine ⟨b, funext fun k => mul_left_cancel₀ hl' ?_⟩
  have h1 : ((PD.p : ℕ) : LetA O n) * a = ((PD.p : ℕ) : LetA O n) * (f * b) := by
    rw [hg, hb]; ring
  exact congrFun h1 k

private theorem aux (W : LocWach PD LL O v n) [IsDomain O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hH : coreH W) (hR : lifta_Ring W) (hA : CaseA W)
    (hφ : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (r s : ℕ → LetA O n)
    (hrs : ∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y)
    (p : W.DD T) (hp : p ∈ pullJ W T i j) :
    ∃ p' ∈ pullJ W T i j, ((PD.p : ℕ) : O) ^ (2 * σ) • p - fMX W M X • p' ∈
      UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan W T i j M X σ := by
  obtain ⟨h1, h2, -, h4, -⟩ := hH hA T hT i
  have hpr : PD.p.Prime := PD.hp
  have hcast : ∀ (k : ℕ) (x : W.DD T),
      ((PD.p : ℕ) : LetA O n) ^ k • x = ((PD.p : ℕ) : O) ^ k • x := by
    intro k x
    rw [← algebraMap_smul (LetA O n) (((PD.p : ℕ) : O) ^ k) x, map_pow, map_natCast]
  have hEe : ∀ y : ℕ, y + padicValNat PD.p y.factorial ≤ eY PD.p y := by
    intro y
    have h := (Rat.cast_le (K := ℝ)).2 (h4 y)
    have h' : ((y + padicValNat PD.p y.factorial : ℕ) : ℝ) ≤ (y : ℝ) * PD.p / ((PD.p : ℝ) - 1) := by
      simpa using h
    exact (Nat.cast_le (α := ℝ)).1 (h'.trans (Nat.le_ceil _))
  have hlam : ∀ k : ℕ, ∃ u : Oˣ, u₁ W ^ (k + 1) - 1 = (u : O) * ((PD.p : ℕ) : O) ^
      (((k + 1) + padicValNat PD.p (k + 1).factorial) - (k + padicValNat PD.p k.factorial)) := by
    intro k
    rw [val_succ PD.p hpr k, Nat.add_sub_cancel_left]
    refine unit_of_val v hinj hO _ _ _ (h2 (k + 1) (by omega)) ?_
    rw [map_pow, map_natCast, v.map_pow, W.v_l, nsmul_one]
  have hser := UpperTheory.filtration_exponent_bound (N0 W T i) (W.γ T) W.π₀ ((PD.p : ℕ) : O)
    (fun y => y + padicValNat PD.p y.factorial) (eY PD.p) (fun k => u₁ W ^ k - 1)
    (monotone_nat_of_le_succ fun k => by have := val_succ PD.p hpr k; omega)
    (eY_mono PD.p hpr) hEe hlam (by simp) (smul_mem_wachFiltration W T i _ hR.πΔ) (fun k x hx => h1 k x hx)
  rw [← hcast]
  refine UpperTheory.divisibility_filtration ((PD.p : ℕ) : LetA O n) (fMX W M X) ((W.φA ^ j) W.π₀) σ (max M X)
    (fun y => y + padicValNat PD.p y.factorial) (eY PD.p) r s _ _ (sat W _ ?_)
    (val_add PD.p hpr) hEe (by simp [eY]) (fun y => (hrs y).1.2) (fun y => (hrs y).2) ?_ ?_ p hp
  · rw [fMX, map_mul, map_pow, map_pow]
    exact (hR.πU.pow _).mul (hR.qU.pow _)
  · intro y hy
    obtain ⟨u, -, -, -, -, hu⟩ := hφ j y
    rw [hu, fMX]
    have hM : M ≤ y := by omega
    have hX : X ≤ (PD.p - 1) * y := by
      have h := hpr.two_le
      have h' : 1 * y ≤ (PD.p - 1) * y := Nat.mul_le_mul_right y (by omega)
      omega
    refine mul_dvd_mul ((pow_dvd_pow _ hM).mul_left u) ((pow_dvd_pow (qp W) hX).trans ?_)
    exact Finset.dvd_prod_of_mem (fun k => pk W k ^ ((PD.p - 1) * y))
      (Finset.mem_range.2 (show 0 < j by omega))
  · rintro _ ⟨w, hw, rfl⟩
    have hw0 : w ∈ N0 W T i := (mem_wachFiltration_iff W T i w).2 hw
    obtain ⟨c, hc0, hc, hK⟩ := hser w hw0
    refine ⟨fun y => ((W.φD T) ^ j) (c y), by simp [hc0],
      fun y => ⟨c y, (mem_wachFiltration_iff W T i _).1 (hc y), rfl⟩, Submodule.subset_span ?_⟩
    refine ⟨w, hw.1, ⟨hw.2, ⟨0, 0, by simpa using hw.1⟩, ?_⟩,
      fun y => ((PD.p : ℕ) : O) ^ (eY PD.p y - (y + padicValNat PD.p y.factorial)) • c y, r, s,
      ⟨by simp [hc0], fun y => ?_, fun k => ?_⟩, hrs, ?_⟩
    · obtain ⟨x', hx', he⟩ := h1 0 w hw0
      exact ⟨x', hx'.1.1, hx'.1.2, by simpa using he⟩
    · exact ((mem_wachFiltration_iff W T i _).1 ((N0 W T i).smul_mem _ (hc y))).symm
    · obtain ⟨t, ht, he⟩ := hK k
      exact ⟨0, t, ht.1.1, ht.1.2, by rw [pow_zero, one_smul]; exact he⟩
    · rw [hcast]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [mul_smul, hcast, map_smul]

end SlopeTestRemainingChoices

theorem UpperTheory.Reformulated.B.IntegerSpanGenerators.span_gen :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] {Qp K₀ K : Type} [inst_2 : Field Qp] [inst_3 : Field K₀]
      [inst_4 : Field K]
      [inst_5 :
        @Algebra Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
          (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3)))]
      [inst_6 :
        @Algebra Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))]
      [inst_7 :
        @Algebra K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4)))]
      [inst_8 :
        @IsScalarTower Qp K₀ K
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_7)
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_6)]
      {B BdR : Type} [inst_9 : CommRing B] [inst_10 : CommRing BdR]
      [inst_11 :
        @Algebra Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))]
      [inst_12 :
        @Algebra K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
          (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9))]
      [inst_13 :
        @IsScalarTower Qp K₀ B
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
          (@Algebra.toSMul K₀ B (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_12)
          (@Algebra.toSMul Qp B (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@CommSemiring.toSemiring B (@CommRing.toCommSemiring B inst_9)) inst_11)]
      [inst_14 :
        @Algebra Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
      [inst_15 :
        @Algebra K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
      [inst_16 :
        @Algebra K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
          (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10))]
      [inst_17 :
        @IsScalarTower Qp K BdR
          (@Algebra.toSMul Qp K (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_6)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_16)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_14)]
      [inst_18 :
        @IsScalarTower K₀ K BdR
          (@Algebra.toSMul K₀ K (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_4))) inst_7)
          (@Algebra.toSMul K BdR (@Semifield.toCommSemiring K (@Field.toSemifield K inst_4))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_16)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_15)]
      [inst_19 :
        @IsScalarTower Qp K₀ BdR
          (@Algebra.toSMul Qp K₀ (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@DivisionSemiring.toSemiring K₀ (@Semifield.toDivisionSemiring K₀ (@Field.toSemifield K₀ inst_3))) inst_5)
          (@Algebra.toSMul K₀ BdR (@Semifield.toCommSemiring K₀ (@Field.toSemifield K₀ inst_3))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_15)
          (@Algebra.toSMul Qp BdR (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
            (@CommSemiring.toSemiring BdR (@CommRing.toCommSemiring BdR inst_10)) inst_14)]
      {PD :
        @Formalism.WeaklyAdmissibleFiltrations.PeriodData G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
          inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19}
      {LL O : Type} [inst_20 : Field LL]
      [inst_21 :
        @Algebra Qp LL (@Semifield.toCommSemiring Qp (@Field.toSemifield Qp inst_2))
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))]
      [inst_22 : TopologicalSpace LL] [inst_23 : CommRing O]
      [inst_24 :
        @Algebra O LL (@CommRing.toCommSemiring O inst_23)
          (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))]
      {v :
        @AddValuation LL (@DivisionRing.toRing LL (@Field.toDivisionRing LL inst_20)) (WithTop Rat)
          (@WithTop.linearOrderedAddCommMonoidWithTop Rat (@AddCommGroup.toAddCancelCommMonoid Rat Rat.addCommGroup)
            Rat.linearOrder Rat.instIsOrderedAddMonoid)}
      {n : Nat}
      (W :
        @Formalism.BasicNotions.LocWach G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
          inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
          inst_22 v n)
      [@NeZero Nat (@MulZeroClass.toZero Nat Nat.instMulZeroClass) n]
      [@IsDomain O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))],
      @Function.Injective O LL
          (@DFunLike.coe
            (@RingHom O LL
              (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))))
            O (fun (x : O) ↦ LL)
            (@RingHom.instFunLike O LL
              (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
              (@Semiring.toNonAssocSemiring LL
                (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))))
            (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_23)
              (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))
              inst_24)) →
        (∀ (x : LL),
            @LE.le (WithTop Rat) (@Preorder.toLE (WithTop Rat) (@WithTop.instPreorder Rat Rat.instPreorder))
                (@OfNat.ofNat (WithTop Rat) (nat_lit 0)
                  (@Zero.toOfNat0 (WithTop Rat)
                    (@WithTop.zero Rat (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)))))
                (@DFunLike.coe
                  (@AddValuation LL (@DivisionRing.toRing LL (@Field.toDivisionRing LL inst_20)) (WithTop Rat)
                    (@WithTop.linearOrderedAddCommMonoidWithTop Rat
                      (@AddCommGroup.toAddCancelCommMonoid Rat Rat.addCommGroup) Rat.linearOrder
                      Rat.instIsOrderedAddMonoid))
                  LL (fun (x : LL) ↦ WithTop Rat)
                  (@AddValuation.instFunLike LL (WithTop Rat) (@DivisionRing.toRing LL (@Field.toDivisionRing LL inst_20))
                    (@WithTop.linearOrderedAddCommMonoidWithTop Rat
                      (@AddCommGroup.toAddCancelCommMonoid Rat Rat.addCommGroup) Rat.linearOrder
                      Rat.instIsOrderedAddMonoid))
                  v x) →
              ∃ (o : O),
                @Eq LL
                  (@DFunLike.coe
                    (@RingHom O LL
                      (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                      (@Semiring.toNonAssocSemiring LL
                        (@DivisionSemiring.toSemiring LL
                          (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))))
                    O (fun (x : O) ↦ LL)
                    (@RingHom.instFunLike O LL
                      (@Semiring.toNonAssocSemiring O (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                      (@Semiring.toNonAssocSemiring LL
                        (@DivisionSemiring.toSemiring LL
                          (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))))
                    (@Algebra.algebraMap O LL (@CommRing.toCommSemiring O inst_23)
                      (@DivisionSemiring.toSemiring LL (@Semifield.toDivisionSemiring LL (@Field.toSemifield LL inst_20)))
                      inst_24)
                    o)
                  x) →
          @Formalism.MainNotions.DeltaInvariantLattices.P9W G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                    inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22
                    inst_23 inst_24 v n W →
            @Formalism.MainNotions.LiftingTheory.coreH G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                      inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22
                      inst_23 inst_24 v n W →
              @Formalism.MainNotions.LiftingTheory.lifta_Ring G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                        inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                        inst_22 inst_23 inst_24 v n W →
                @Formalism.MainNotions.ArcLiftingSetup.SATPcore G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                          inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 LL O inst_20 inst_21
                          inst_22 inst_23 inst_24 v n PD W →
                  @Formalism.MainNotions.LiftingTheory.CaseA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9
                            inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                            inst_21 inst_22 inst_23 inst_24 v n W →
                    (∀ (j r : Nat),
                        ∃ (u : @Formalism.BasicNotions.LetA O inst_23 n),
                          And
                            (@Membership.mem (@Formalism.BasicNotions.LetA O inst_23 n)
                              (@Subalgebra O (@Formalism.BasicNotions.LetA O inst_23 n) (@CommRing.toCommSemiring O inst_23)
                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                  @MvPowerSeries.instSemiring Unit O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                  (@MvPowerSeries.instSemiring Unit O
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                  (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                    (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                              (@SetLike.instMembership
                                (@Subalgebra O (@Formalism.BasicNotions.LetA O inst_23 n) (@CommRing.toCommSemiring O inst_23)
                                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                    @MvPowerSeries.instSemiring Unit O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                  (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                    (@MvPowerSeries.instSemiring Unit O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                    (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                      (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                (@Formalism.BasicNotions.LetA O inst_23 n)
                                (@Subalgebra.instSetLike O (@Formalism.BasicNotions.LetA O inst_23 n) (@CommRing.toCommSemiring O inst_23)
                                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                    @MvPowerSeries.instSemiring Unit O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                  (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                    (@MvPowerSeries.instSemiring Unit O
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                    (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                      (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))))
                              (@Formalism.BasicNotions.LocWach.AΔ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B
                                BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19
                                PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W)
                              u)
                            (∃ (u' : @Formalism.BasicNotions.LetA O inst_23 n),
                              And
                                (@Membership.mem (@Formalism.BasicNotions.LetA O inst_23 n)
                                  (@Subalgebra O (@Formalism.BasicNotions.LetA O inst_23 n) (@CommRing.toCommSemiring O inst_23)
                                    (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                      @MvPowerSeries.instSemiring Unit O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                    (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                      (@MvPowerSeries.instSemiring Unit O
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                      (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                        (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                        (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                  (@SetLike.instMembership
                                    (@Subalgebra O (@Formalism.BasicNotions.LetA O inst_23 n) (@CommRing.toCommSemiring O inst_23)
                                      (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                        @MvPowerSeries.instSemiring Unit O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                      (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                        (@MvPowerSeries.instSemiring Unit O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                        (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                          (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                    (@Formalism.BasicNotions.LetA O inst_23 n)
                                    (@Subalgebra.instSetLike O (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@CommRing.toCommSemiring O inst_23)
                                      (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                        @MvPowerSeries.instSemiring Unit O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                      (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                        (@MvPowerSeries.instSemiring Unit O
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                        (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                          (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))))
                                  (@Formalism.BasicNotions.LocWach.AΔ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                    inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                    inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W)
                                  u')
                                (And
                                  (@Eq (@Formalism.BasicNotions.LetA O inst_23 n)
                                    (@HMul.hMul (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@instHMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@Pi.instMul (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                          @MvPowerSeries.instMul Unit O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                      u u')
                                    (@OfNat.ofNat (@Formalism.BasicNotions.LetA O inst_23 n) (nat_lit 1)
                                      (@One.toOfNat1 (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@Pi.instOne (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                          @MvPowerSeries.instOne Unit O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))))
                                  (@Eq (@Formalism.BasicNotions.LetA O inst_23 n)
                                    (@HPow.hPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@instHPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat
                                        (@Pi.instPow (ZMod n) Nat (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                          @NPow.toPow (PowerSeries O)
                                            (@Monoid.toNPow (PowerSeries O)
                                              (@Semiring.toMonoid (PowerSeries O)
                                                (@MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))))))
                                      (@DFunLike.coe
                                        (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@CommRing.toCommSemiring O inst_23)
                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                          (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                            (@MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                              (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                          (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                            (@MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                              (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                        (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (fun (x : @Formalism.BasicNotions.LetA O inst_23 n) ↦ @Formalism.BasicNotions.LetA O inst_23 n)
                                        (@AlgHom.funLike O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@CommRing.toCommSemiring O inst_23)
                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                          (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                            (@MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                              (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                          (@Function.algebra O (ZMod n) (PowerSeries O) (@CommRing.toCommSemiring O inst_23)
                                            (@MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                              (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                        (@HPow.hPow
                                          (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@CommRing.toCommSemiring O inst_23)
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@Function.algebra O (ZMod n) (PowerSeries O)
                                              (@CommRing.toCommSemiring O inst_23)
                                              (@MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                            (@Function.algebra O (ZMod n) (PowerSeries O)
                                              (@CommRing.toCommSemiring O inst_23)
                                              (@MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                          Nat
                                          (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@CommRing.toCommSemiring O inst_23)
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@Function.algebra O (ZMod n) (PowerSeries O)
                                              (@CommRing.toCommSemiring O inst_23)
                                              (@MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                            (@Function.algebra O (ZMod n) (PowerSeries O)
                                              (@CommRing.toCommSemiring O inst_23)
                                              (@MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                          (@instHPow
                                            (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                              (@CommRing.toCommSemiring O inst_23)
                                              (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                @MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                @MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@Function.algebra O (ZMod n) (PowerSeries O)
                                                (@CommRing.toCommSemiring O inst_23)
                                                (@MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                  (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                              (@Function.algebra O (ZMod n) (PowerSeries O)
                                                (@CommRing.toCommSemiring O inst_23)
                                                (@MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                  (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                            Nat
                                            (@NPow.toPow
                                              (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@CommRing.toCommSemiring O inst_23)
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@Function.algebra O (ZMod n) (PowerSeries O)
                                                  (@CommRing.toCommSemiring O inst_23)
                                                  (@MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                  (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                    (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                                (@Function.algebra O (ZMod n) (PowerSeries O)
                                                  (@CommRing.toCommSemiring O inst_23)
                                                  (@MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                  (@MvPowerSeries.instAlgebra Unit O O (@CommRing.toCommSemiring O inst_23)
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                    (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                              (@Monoid.toNPow
                                                (@AlgHom O (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                                  (@CommRing.toCommSemiring O inst_23)
                                                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                    fun (i : ZMod n) ↦
                                                    @MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                    fun (i : ZMod n) ↦
                                                    @MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                  (@Function.algebra O (ZMod n) (PowerSeries O)
                                                    (@CommRing.toCommSemiring O inst_23)
                                                    (@MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                    (@MvPowerSeries.instAlgebra Unit O O
                                                      (@CommRing.toCommSemiring O inst_23)
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                      (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))
                                                  (@Function.algebra O (ZMod n) (PowerSeries O)
                                                    (@CommRing.toCommSemiring O inst_23)
                                                    (@MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                    (@MvPowerSeries.instAlgebra Unit O O
                                                      (@CommRing.toCommSemiring O inst_23)
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                      (@Algebra.id O (@CommRing.toCommSemiring O inst_23)))))
                                                (@AlgHom.End O (@Formalism.BasicNotions.LetA O inst_23 n)
                                                  (@CommRing.toCommSemiring O inst_23)
                                                  (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                    fun (i : ZMod n) ↦
                                                    @MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                  (@Function.algebra O (ZMod n) (PowerSeries O)
                                                    (@CommRing.toCommSemiring O inst_23)
                                                    (@MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                    (@MvPowerSeries.instAlgebra Unit O O
                                                      (@CommRing.toCommSemiring O inst_23)
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                      (@Algebra.id O (@CommRing.toCommSemiring O inst_23))))))))
                                          (@Formalism.BasicNotions.LocWach.φA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                            inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                            inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22
                                            v n W)
                                          j)
                                        (@Formalism.BasicNotions.LocWach.π₀ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                          inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16
                                          inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W))
                                      r)
                                    (@HMul.hMul (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@Formalism.BasicNotions.LetA O inst_23 n)
                                      (@instHMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@Pi.instMul (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                          @MvPowerSeries.instMul Unit O
                                            (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                      (@HMul.hMul (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@instHMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@Pi.instMul (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instMul Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                        u
                                        (@HPow.hPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@instHPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat
                                            (@Pi.instPow (ZMod n) Nat (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @NPow.toPow (PowerSeries O)
                                                (@Monoid.toNPow (PowerSeries O)
                                                  (@Semiring.toMonoid (PowerSeries O)
                                                    (@MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))))))
                                          (@Formalism.BasicNotions.LocWach.π₀ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                            inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                            inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22
                                            v n W)
                                          r))
                                      (∏ k ∈ Finset.range j,
                                        @HPow.hPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@instHPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat
                                            (@Pi.instPow (ZMod n) Nat (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @NPow.toPow (PowerSeries O)
                                                (@Monoid.toNPow (PowerSeries O)
                                                  (@Semiring.toMonoid (PowerSeries O)
                                                    (@MvPowerSeries.instSemiring Unit O
                                                      (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))))))
                                          (@Formalism.MainNotions.LiftingTheory.pk G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                            inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16
                                            inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22 inst_23 inst_24 v n W k)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat)
                                              (@Formalism.WeaklyAdmissibleFiltrations.PeriodData.p G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD)
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            r))))))) →
                      ∀ (T : @Formalism.BasicNotions.LocLat G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22),
                        @Formalism.WeaklyAdmissibleFiltrations.IsCrys G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                  inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL inst_20 inst_21
                                  (@Formalism.BasicNotions.LocLat.V G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T)
                                  (@Formalism.BasicNotions.LocLat.acg G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T)
                                  (@Formalism.BasicNotions.LocLat.modLL G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T)
                                  (@Formalism.BasicNotions.LocLat.modQp G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T)
                                  (@Formalism.BasicNotions.LocLat.towQp G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T)
                                  (@Formalism.BasicNotions.LocLat.ρ G inst inst_1 Qp LL O inst_2 inst_20 inst_21 inst_23 inst_24 inst_22 T) →
                          ∀ (i : ZMod n) {j M X σ : Nat},
                            @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
                              ∀ (r s : Nat → @Formalism.BasicNotions.LetA O inst_23 n),
                                (∀ (y : Nat),
                                    And
                                      (@Formalism.MainNotions.CrystallineLiftingInputs.IsRem G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                        inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                        inst_18 inst_19 PD LL O inst_20 inst_21 inst_22 inst_23 inst_24 v n W j M X y (r y))
                                      (@Eq (@Formalism.BasicNotions.LetA O inst_23 n)
                                        (@HMul.hMul (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@instHMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@Pi.instMul (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instMul Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                          (@HPow.hPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@instHPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat
                                              (@Pi.instPow (ZMod n) Nat (fun (a : ZMod n) ↦ PowerSeries O)
                                                fun (i : ZMod n) ↦
                                                @NPow.toPow (PowerSeries O)
                                                  (@Monoid.toNPow (PowerSeries O)
                                                    (@Semiring.toMonoid (PowerSeries O)
                                                      (@MvPowerSeries.instSemiring Unit O
                                                        (@CommSemiring.toSemiring O
                                                          (@CommRing.toCommSemiring O inst_23)))))))
                                            (@Nat.cast (@Formalism.BasicNotions.LetA O inst_23 n)
                                              (@Pi.instNatCast (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                fun (a : ZMod n) ↦
                                                @AddMonoidWithOne.toNatCast (PowerSeries O)
                                                  (@MvPowerSeries.instAddMonoidWithOne Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                              (@Formalism.WeaklyAdmissibleFiltrations.PeriodData.p G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD))
                                            (Formalism.MainNotions.CrystallineLiftingInputs.eY
                                              (@Formalism.WeaklyAdmissibleFiltrations.PeriodData.p G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD)
                                              y))
                                          (s y))
                                        (@HMul.hMul (@Formalism.BasicNotions.LetA O inst_23 n) (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@instHMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@Pi.instMul (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instMul Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                          (@HPow.hPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@instHPow (@Formalism.BasicNotions.LetA O inst_23 n) Nat
                                              (@Pi.instPow (ZMod n) Nat (fun (a : ZMod n) ↦ PowerSeries O)
                                                fun (i : ZMod n) ↦
                                                @NPow.toPow (PowerSeries O)
                                                  (@Monoid.toNPow (PowerSeries O)
                                                    (@Semiring.toMonoid (PowerSeries O)
                                                      (@MvPowerSeries.instSemiring Unit O
                                                        (@CommSemiring.toSemiring O
                                                          (@CommRing.toCommSemiring O inst_23)))))))
                                            (@Nat.cast (@Formalism.BasicNotions.LetA O inst_23 n)
                                              (@Pi.instNatCast (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                fun (a : ZMod n) ↦
                                                @AddMonoidWithOne.toNatCast (PowerSeries O)
                                                  (@MvPowerSeries.instAddMonoidWithOne Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))))
                                              (@Formalism.WeaklyAdmissibleFiltrations.PeriodData.p G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD))
                                            σ)
                                          (r y)))) →
                                  ∀
                                    (p :
                                      @Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                        inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                        inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W T),
                                    @Membership.mem
                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                          inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16
                                          inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                        (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                            inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                            inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22
                                            v n W T)
                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                            @MvPowerSeries.instSemiring Unit O
                                              (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                          (@AddCommGroup.toAddCommMonoid
                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                              inst_22 v n W T)
                                            (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                              inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                              inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                              inst_24 inst_22 v n W T))
                                          (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                            inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                            inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22
                                            v n W T))
                                        (@SetLike.instMembership
                                          (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                              inst_22 v n W T)
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@AddCommGroup.toAddCommMonoid
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                inst_24 inst_22 v n W T))
                                            (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                              inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                              inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                              inst_24 inst_22 v n W T))
                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                            inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                            inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22
                                            v n W T)
                                          (@Submodule.setLike (@Formalism.BasicNotions.LetA O inst_23 n)
                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                              inst_22 v n W T)
                                            (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                              @MvPowerSeries.instSemiring Unit O
                                                (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                            (@AddCommGroup.toAddCommMonoid
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                inst_24 inst_22 v n W T))
                                            (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                              inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                              inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                              inst_24 inst_22 v n W T)))
                                        (@Formalism.MainNotions.CrystallineLiftingInputs.pullJ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                          inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16
                                          inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22 inst_23 inst_24 v n W T i
                                          j)
                                        p →
                                      ∃ (p' :
                                        @Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6 inst_7
                                          inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15 inst_16
                                          inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W T),
                                        And
                                          (@Membership.mem
                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                              inst_22 v n W T)
                                            (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                @MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@AddCommGroup.toAddCommMonoid
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T))
                                              (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                inst_24 inst_22 v n W T))
                                            (@SetLike.instMembership
                                              (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@AddCommGroup.toAddCommMonoid
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T))
                                                (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T))
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Submodule.setLike (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@AddCommGroup.toAddCommMonoid
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T))
                                                (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)))
                                            (@Formalism.MainNotions.CrystallineLiftingInputs.pullJ G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22 inst_23
                                              inst_24 v n W T i j)
                                            p')
                                          (@Membership.mem
                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                              inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                              inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                              inst_22 v n W T)
                                            (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                @MvPowerSeries.instSemiring Unit O
                                                  (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                              (@AddCommGroup.toAddCommMonoid
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T))
                                              (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                inst_24 inst_22 v n W T))
                                            (@SetLike.instMembership
                                              (@Submodule (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@AddCommGroup.toAddCommMonoid
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T))
                                                (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T))
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Submodule.setLike (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O) fun (i : ZMod n) ↦
                                                  @MvPowerSeries.instSemiring Unit O
                                                    (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                (@AddCommGroup.toAddCommMonoid
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T))
                                                (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)))
                                            (@UpperTheory.Reformulated.B.IntegerSpanGenerators.Zspan G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                              inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                              inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22
                                              inst_23 inst_24 v n W T i j M X σ)
                                            (@HSub.hSub
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                inst_22 v n W T)
                                              (@instHSub
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@SubNegMonoid.toSub
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@AddGroup.toSubNegMonoid
                                                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                      inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                      inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                                                      inst_21 inst_23 inst_24 inst_22 v n W T)
                                                    (@AddCommGroup.toAddGroup
                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                      (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)))))
                                              (@HSMul.hSMul O
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@instHSMul O
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@SMulZeroClass.toSMul O
                                                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                      inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                      inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                                                      inst_21 inst_23 inst_24 inst_22 v n W T)
                                                    (@AddZero.toZero
                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                      (@AddZeroClass.toAddZero
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@AddMonoid.toAddZeroClass
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@SubNegMonoid.toAddMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddGroup.toSubNegMonoid
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@AddCommGroup.toAddGroup
                                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                  inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                  inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                  inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                  inst_22 v n W T)
                                                                (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                  inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                  inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                  inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                  inst_22 v n W T)))))))
                                                    (@DistribSMul.toSMulZeroClass O
                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                      (@AddMonoid.toAddZeroClass
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@SubNegMonoid.toAddMonoid
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@AddGroup.toSubNegMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddCommGroup.toAddGroup
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)))))
                                                      (@DistribMulAction.toDistribSMul O
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@Semiring.toMonoid O
                                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23)))
                                                        (@SubNegMonoid.toAddMonoid
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@AddGroup.toSubNegMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddCommGroup.toAddGroup
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T))))
                                                        (@Module.toDistribMulAction O
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@CommSemiring.toSemiring O (@CommRing.toCommSemiring O inst_23))
                                                          (@AddCommGroup.toAddCommMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                              inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                              inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                              inst_22 v n W T))
                                                          (@Formalism.BasicNotions.LocWach.ddModO G inst inst_1 Qp K₀ K inst_2 inst_3
                                                            inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                            inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19
                                                            PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W T))))))
                                                (@HPow.hPow O Nat O
                                                  (@instHPow O Nat
                                                    (@NPow.toPow O
                                                      (@Monoid.toNPow O
                                                        (@Semiring.toMonoid O
                                                          (@CommSemiring.toSemiring O
                                                            (@CommRing.toCommSemiring O inst_23))))))
                                                  (@Nat.cast O
                                                    (@AddMonoidWithOne.toNatCast O
                                                      (@AddGroupWithOne.toAddMonoidWithOne O
                                                        (@Ring.toAddGroupWithOne O (@CommRing.toRing O inst_23))))
                                                    (@Formalism.WeaklyAdmissibleFiltrations.PeriodData.p G inst Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                      inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                      inst_15 inst_16 inst_17 inst_18 inst_19 PD))
                                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) σ))
                                                p)
                                              (@HSMul.hSMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                  inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14
                                                  inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_23
                                                  inst_24 inst_22 v n W T)
                                                (@instHSMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                                  (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                    inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                    inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21
                                                    inst_23 inst_24 inst_22 v n W T)
                                                  (@SMulZeroClass.toSMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                                    (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5
                                                      inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13
                                                      inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O inst_20
                                                      inst_21 inst_23 inst_24 inst_22 v n W T)
                                                    (@AddZero.toZero
                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                      (@AddZeroClass.toAddZero
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@AddMonoid.toAddZeroClass
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@SubNegMonoid.toAddMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddGroup.toSubNegMonoid
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@AddCommGroup.toAddGroup
                                                                (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                  inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                  inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                  inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                  inst_22 v n W T)
                                                                (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                  inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                  inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                  inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                  inst_22 v n W T)))))))
                                                    (@DistribSMul.toSMulZeroClass (@Formalism.BasicNotions.LetA O inst_23 n)
                                                      (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                        inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                        inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                        inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                      (@AddMonoid.toAddZeroClass
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@SubNegMonoid.toAddMonoid
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@AddGroup.toSubNegMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddCommGroup.toAddGroup
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)))))
                                                      (@DistribMulAction.toDistribSMul (@Formalism.BasicNotions.LetA O inst_23 n)
                                                        (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                          inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                          inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                          inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                        (@Pi.monoid (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                          fun (i : ZMod n) ↦
                                                          @Semiring.toMonoid (PowerSeries O)
                                                            (@MvPowerSeries.instSemiring Unit O
                                                              (@CommSemiring.toSemiring O
                                                                (@CommRing.toCommSemiring O inst_23))))
                                                        (@SubNegMonoid.toAddMonoid
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@AddGroup.toSubNegMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@AddCommGroup.toAddGroup
                                                              (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T)
                                                              (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                                inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                                inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                                inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                                inst_22 v n W T))))
                                                        (@Module.toDistribMulAction (@Formalism.BasicNotions.LetA O inst_23 n)
                                                          (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                            inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12
                                                            inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19 PD LL O
                                                            inst_20 inst_21 inst_23 inst_24 inst_22 v n W T)
                                                          (@Pi.semiring (ZMod n) (fun (a : ZMod n) ↦ PowerSeries O)
                                                            fun (i : ZMod n) ↦
                                                            @MvPowerSeries.instSemiring Unit O
                                                              (@CommSemiring.toSemiring O
                                                                (@CommRing.toCommSemiring O inst_23)))
                                                          (@AddCommGroup.toAddCommMonoid
                                                            (@Formalism.BasicNotions.LocWach.DD G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4
                                                              inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                              inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18
                                                              inst_19 PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W
                                                              T)
                                                            (@Formalism.BasicNotions.LocWach.ddAcg G inst inst_1 Qp K₀ K inst_2 inst_3
                                                              inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10
                                                              inst_11 inst_12 inst_13 inst_14 inst_15 inst_16 inst_17
                                                              inst_18 inst_19 PD LL O inst_20 inst_21 inst_23 inst_24
                                                              inst_22 v n W T))
                                                          (@Formalism.BasicNotions.LocWach.ddModA G inst inst_1 Qp K₀ K inst_2 inst_3
                                                            inst_4 inst_5 inst_6 inst_7 inst_8 B BdR inst_9 inst_10 inst_11
                                                            inst_12 inst_13 inst_14 inst_15 inst_16 inst_17 inst_18 inst_19
                                                            PD LL O inst_20 inst_21 inst_23 inst_24 inst_22 v n W T))))))
                                                (@Formalism.MainNotions.CrystallineLiftingInputs.fMX G inst inst_1 Qp K₀ K inst_2 inst_3 inst_4 inst_5 inst_6
                                                  inst_7 inst_8 B BdR inst_9 inst_10 inst_11 inst_12 inst_13 inst_14 inst_15
                                                  inst_16 inst_17 inst_18 inst_19 PD LL O inst_20 inst_21 inst_22 inst_23
                                                  inst_24 v n W M X)
                                                p'))) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W _ _ hinj hO _ hH hR _ hA hφ
    T hT i j M X σ hj r s hrs p hp
  exact aux W hinj hO hH hR hA hφ T hT i hj r s hrs p hp
