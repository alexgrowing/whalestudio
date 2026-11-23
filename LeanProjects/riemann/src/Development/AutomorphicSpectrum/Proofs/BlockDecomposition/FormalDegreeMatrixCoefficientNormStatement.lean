import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNorm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_degree_matrix_coefficient_norm : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp | exact GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp | (intros; apply GlobalTheory.CompanionTheory.RgHeA.CoefHS.isHilbertSchmidt_coefOp <;> assumption)
