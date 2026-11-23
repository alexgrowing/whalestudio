import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieSkewAdjointBis
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleDiscreteSpaces

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | exact GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map <;> assumption)
