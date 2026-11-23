import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStable
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
theorem _root_.GlobalTheory.T.exists_finite_dim_compact_stable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) → ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧ (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧ ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | exact GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace | (intros; apply GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace <;> assumption)
