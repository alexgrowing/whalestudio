import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinerContractionOnePlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqMulProdOfPartial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiner_contraction_one_place : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) [DecidableEq D.what₂.Tau], IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.CompactFock ψ θ M M' ω f τ aS aT → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.LieFock ψ θ M M' ω f τ aS aT → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ (v : M'.Vec) (w : ∀ ρ, M.H ρ), ∃ A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ, SemiW M M' τ aS aT A ∧ ∀ φ y u, ⟪u, A φ y⟫_ℂ = ellT M (Function.update w τ u) (inclT M (It φ (PiTensorProduct.tprod ℂ (Function.update v τ y)))) := by
  first | exact @GlobalTheory.Chain.RealLine.Semi.exists_semiW | exact GlobalTheory.Chain.RealLine.Semi.exists_semiW | (intros; apply GlobalTheory.Chain.RealLine.Semi.exists_semiW <;> assumption)
