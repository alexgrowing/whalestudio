import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.HostOrbitsPlaces
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.CoboundaryTransfers.Statement
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Formalism.FrobeniusOrbits.Statement
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.StatementD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.RealPlaceAnalysis.StatementC

namespace Bl.general_b_fact_left_version

theorem goal1 :
  ∀ {O : Type} [inst : CommRing.{0} O]
  [inst_1 : @IsDomain.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))] {V : Type}
  [inst_2 : AddCommGroup.{0} V]
  [inst_3 :
    @Module.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
      (@OreLocalization.instSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_4 :
    @Module.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_5 :
    @IsScalarTower.{0, 0, 0} O (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
      (@OreLocalization.instSMulOfIsScalarTower.{0, 0, 0} O O O
        (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
        (@nonZeroDivisors.{0} O
          (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
        (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@Monoid.toMulAction.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst)))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        (@instSMulOfMul.{0} O
          (@Distrib.toMul.{0} O
            (@instDistribOfSemiring.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
        _ _)
      (@SMulZeroClass.toSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
            (@OreLocalization.instMonoid.{0} O (@CommMonoid.toMonoid.{0} O (@CommRing.toCommMonoid.{0} O inst))
              (@nonZeroDivisors.{0} O
                (@Semiring.toMonoidWithZero.{0} O
                  (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
              (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
              (@OreLocalization.instSemiring.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@nonZeroDivisors.{0} O
                  (@Semiring.toMonoidWithZero.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
                (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
                  (@nonZeroDivisors.{0} O
                    (@Semiring.toMonoidWithZero.{0} O
                      (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3))))
      (@SMulZeroClass.toSMul.{0, 0} O V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} O V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} O V
            (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} O V
              (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))))]
  (M :
    @Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4),
  @Eq.{1}
      (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
        (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
          (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)
      (@Formalism.MainNotions.G.MQ.{0, 0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V (@FractionRing.field.{0} O inst inst_1) inst_2 inst_3 O
        inst inst_4
        (@OreLocalization.instAlgebra.{0, 0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
          (@nonZeroDivisors.{0} O
            (@Semiring.toMonoidWithZero.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))))
          (@OreLocalization.oreSetComm.{0} O (@CommRing.toCommMonoid.{0} O inst)
            (@nonZeroDivisors.{0} O
              (@Semiring.toMonoidWithZero.{0} O
                (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))
          O (@CommRing.toCommSemiring.{0} O inst) (@Algebra.id.{0} O (@CommRing.toCommSemiring.{0} O inst)))
        inst_5 M)
      (@Top.top.{0}
        (@Submodule.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)
        (@Submodule.instTop.{0, 0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) V
          (@DivisionSemiring.toSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
            (@Semifield.toDivisionSemiring.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1)
              (@Field.toSemifield.{0} (@Formalism.MainNotions.G.KK.{0} O inst inst_1) (@FractionRing.field.{0} O inst inst_1))))
          (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)) →
    ∀ (x : V),
      @Exists.{1} O fun (a : O) ↦
        And
          (@Ne.{1} O a
            (@OfNat.ofNat.{0} O (nat_lit 0)
              (@Zero.toOfNat0.{0} O
                (@MulZeroClass.toZero.{0} O
                  (@instMulZeroClassOfSemiring.{0} O
                    (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))))))
          (@Membership.mem.{0, 0} V
            (@Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
              V
              (@Submodule.setLike.{0, 0} O V (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))
            M
            (@HSMul.hSMul.{0, 0, 0} O V V
              (@instHSMul.{0, 0} O V
                (@SMulZeroClass.toSMul.{0, 0} O V
                  (@AddZero.toZero.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} O V
                    (@AddMonoid.toAddZeroClass.{0} V
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
                    (@DistribMulAction.toDistribSMul.{0, 0} O V
                      (@Semiring.toMonoid.{0} O (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst)))
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
                      (@Module.toDistribMulAction.{0, 0} O V
                        (@CommSemiring.toSemiring.{0} O (@CommRing.toCommSemiring.{0} O inst))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)))))
              a x)) := by
  intro O _ _ V _ _ _ _ M hM x
  have hx : x ∈ Submodule.span (Formalism.MainNotions.G.KK O) (M : Set V) := by
    have h : x ∈ (⊤ : Submodule (Formalism.MainNotions.G.KK O) V) := Submodule.mem_top
    rw [← hM] at h
    exact h
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨b, hb, hby⟩ := hy
    obtain ⟨⟨n, d⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) k
    have hd : (d : O) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨b * d, mul_ne_zero hb hd, ?_⟩
    have key : (d : O) • (IsLocalization.mk' (Formalism.MainNotions.G.KK O) n d • y) = n • y := by
      rw [← smul_assoc, Algebra.smul_def, IsLocalization.mk'_spec', algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact M.smul_mem n hby

end Bl.general_b_fact_left_version
