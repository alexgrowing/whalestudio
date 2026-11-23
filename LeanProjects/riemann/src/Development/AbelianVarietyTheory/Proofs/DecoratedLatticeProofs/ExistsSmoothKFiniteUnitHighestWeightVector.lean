import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPowStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealZetaSmoothHi

theorem exists_smooth_highestUnit : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ w : M.H τ, w ∈ M.sm τ ∧ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ ∧ IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) w := by
  intro h D V S M τ
  obtain ⟨hC, hN, hU, hI, -, ⟨K, hK⟩, -⟩ := M.ds τ
  haveI := hC
  obtain ⟨v, hv, hv0, hw⟩ := hK.2.2.2.1
  have hwS : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := K.smul_mem _ hv
  have hKf : IsKFin (M.ε τ) (M.σ τ) (((‖v‖⁻¹ : ℝ) : ℂ) • v) := ⟨K, hK.1, hwS, hK.2.1⟩
  refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_, ?_, ?_, ?_⟩
  · refine Submodule.subset_span ?_
    exact h.smoothVec hU hI hKf (M.fr_unit τ) (M.fr_gram τ)
  · exact Submodule.subset_span hKf
  · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)
  · exact (le_sSup hK : K ≤ lowKSub (M.ε τ) (M.lam τ) (M.σ τ)) hwS
  · intro θ hθ
    rw [map_smul, hw θ hθ, smul_comm]

end GlobalTheory.RealZetaSmoothHi
