import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionCompTransposeInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_action_comp_transposeInv : ∀ (F : archSmooth ℚ 3) (c : G3) (i j : Fin 3) (h : IsArchSmooth (fun g : G3 => (F : G3 → ℂ) (c * ti g))),
  ((EA i j ⟨fun g : G3 => (F : G3 → ℂ) (c * ti g), h⟩ : archSmooth ℚ 3) : G3 → ℂ) =
    fun g : G3 => -((EA j i F : archSmooth ℚ 3) : G3 → ℂ) (c * ti g) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv.EA_comp_ti | exact GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv.EA_comp_ti | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.TiDeriv.EA_comp_ti <;> assumption)
