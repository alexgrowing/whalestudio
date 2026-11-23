import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalityOfLatticeCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfDiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedColumnAverageExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnMirabolicHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CMEqZeroOfNe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEqOneOfIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageHermitianPositive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageQuasiInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulMemInteger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitOfOneAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinalFormBesselBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvMulMemIntegralGLOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffEqPowOfMulOneSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoZeroOfSumSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipCMemIntegralGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinusculeSetEqDoubleCoset
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitForm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTranslateNeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemCongruenceSubgroupOfDiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUnipBOfMemUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetShalikaBoundOfSteps

namespace PositivityTheory.JacquetShalikaLocal

theorem l0 : L0 := (@GlobalTheory.CompanionTheory.JSBound.l0 : L0)

theorem l1 : L1 := (@GlobalTheory.CompanionTheory.SatakeBound.orthogonality_of_lattice_character : L0 → L1) l0

theorem l2 : L2 := (@GlobalTheory.CompanionTheory.SatakeBound.LargeLattice.stability : L0 → L1 → L2) l0 l1

theorem l3 : L3 := (@GlobalTheory.CompanionTheory.SatakeBound.twisted_column_average_exists : L0 → L3) l0

theorem l3c : ColumnsMirabolic := (@GlobalTheory.CompanionTheory.JSBound.column_mirabolic_holds : ColumnsMirabolic)

theorem l3d : ColumnsUnipotent := (@GlobalTheory.CompanionTheory.JSBound.ColumnUnipotent.main : ColumnsUnipotent)

theorem l4s : FormCoefficientStability := (@GlobalTheory.CompanionTheory.JSBound.stability_coefficients : L0 → L2 → ColumnsMirabolic → FormCoefficientStability) l0 l2 l3c

theorem l4a : StableAverageExists := (@GlobalTheory.CompanionTheory.SatakeStable.stable_average : L0 → FormCoefficientStability → StableAverageExists) l0 l4s

theorem l4b : FormHermitianPositive := (@GlobalTheory.CompanionTheory.JSBoundStep.column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive) l0 l3 l3c

theorem l4c : FormQuasiInvariantMirabolic := (@GlobalTheory.CompanionTheory.JSBound.column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic) l0 l3c l4s

theorem l4d : FormEquivariantColumn := (@GlobalTheory.CompanionTheory.SatakeBound.equivariant_of_steps : L0 → ColumnsMirabolic → ColumnsUnipotent → FormCoefficientStability → FormEquivariantColumn) l0 l3c l3d l4s

theorem l5 : L5 := (@GlobalTheory.CompanionTheory.SatakeBessel.bessel_step : L0 → L1 → L2 → L3 → ColumnsMirabolic → L5) l0 l1 l2 l3 l3c

theorem l6 : L6 := (@GlobalTheory.CompanionTheory.SatakeBound.final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6) l4a l4b l4c l4d l5

theorem l7 : L7 := (@GlobalTheory.CompanionTheory.SatakeBound.heckeEigenvector_whittaker : L7)

theorem l8 : L8 := (@GlobalTheory.CompanionTheory.SatakeBound.schur_row_recursion : L8)

theorem l9 : liftZP_newton := (@GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton)

theorem l10 : ParameterUpperBound := (@GlobalTheory.CompanionTheory.Satake.l10 : L6 → L7 → L8 → liftZP_newton → ParameterUpperBound) l6 l7 l8 l9

theorem l11 : liftZP_unit := (@GlobalTheory.CompanionTheory.SatakeStable.l11 : liftZP_unit)

theorem l11b : ParameterAbsoluteValues := (@GlobalTheory.CompanionTheory.JSBound.symmetric_function_absolute_values : ParameterAbsoluteValues)

theorem l12 : lift_levelP_alt₂ := (@GlobalTheory.CompanionTheory.SatakeTyping.l12 : lift_levelP_alt₂)

theorem g1 : G1 := (@GlobalTheory.CompanionTheory.JSUnit.exists_unit_form : G1)

theorem g2 : G2 := (@GlobalTheory.CompanionTheory.SatakeBound.exists_translate_ne_zero : G2)

theorem g3 : G3 := (@GlobalTheory.CompanionTheory.JSSmooth.g3 : G3)

theorem g4 : G4 := (@GlobalTheory.CompanionTheory.JSBound.global_character_holds : G4)

theorem jacquetShalikaBound : GlobalTheory.Published.JacquetShalikaBound := (@GlobalTheory.CompanionTheory.SatakeBound.jacquetShalikaBound_of_steps : ParameterUpperBound → liftZP_unit → ParameterAbsoluteValues → lift_levelP_alt₂ → G1 → G2 → G3 → G4 → GlobalTheory.Published.JacquetShalikaBound) l10 l11 l11b l12 g1 g2 g3 g4

theorem jacquetShalika_of (h : GlobalTheory.Published.JacquetShalikaRigidity) : GlobalTheory.Published.JacquetShalika := ⟨h, jacquetShalikaBound⟩

end PositivityTheory.JacquetShalikaLocal
