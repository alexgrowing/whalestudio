import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  intro D θ hθ V hV S M
  refine ⟨GlobalTheory.ChainOnto.RealData.sortedFrame M hV, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame M hV,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart M hV τ, ?_⟩
  intro J χ U hU v hv
  induction hU using Submodule.span_induction with
  | mem T hT =>
    exact GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hT.aut v, hT.cusp v⟩,
      GlobalTheory.ChainOnto.RealData.isKFinite_value θ hθ M hV hT v hv⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact (GlobalTheory.Cusp.A0 θ V _).smul_mem a hx

end
