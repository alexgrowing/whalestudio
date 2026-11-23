import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspForms
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicity_map_apply_mem_A0_of_kfin : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  first | exact @GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | exact GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms | (intros; apply GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms <;> assumption)
