import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMap
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ → (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin n) (Fin n) ℂ), OntoUni r → ∀ (y : Frames G) (yk : K → Frames G), (∀ k, ∃ kt, (∀ τ, GlobalTheory.BranchFormula.IsBlock hN (kt τ) (r k τ) 1) ∧ IsTr kt y (yk k)) → ∀ J ∈ ValC G' sg, ∀ Jk : K → Frames G' → ℂ, (∀ k z z', IsTr (r k) z z' → Jk k z' = J z) → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ∫ k, ℓ (Jk k) * Φ (yk k) ∂ν = c * ℓ (T₀ Φ) := by
  first | exact @GlobalTheory.KJAvg.avg_eq_mul_branch | exact GlobalTheory.KJAvg.avg_eq_mul_branch | (intros; apply GlobalTheory.KJAvg.avg_eq_mul_branch <;> assumption)
