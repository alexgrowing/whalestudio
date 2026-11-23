import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchSmoothCompTransposeInv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archSmooth_comp_transposeInv : ∀ (F : G3 → ℂ), IsArchSmooth F → ∀ c : G3, IsArchSmooth (fun g : G3 => F (c * ti g)) := by
  first | exact @GlobalTheory.CompanionTheory.TiArch.isArchSmooth_comp_ti | exact GlobalTheory.CompanionTheory.TiArch.isArchSmooth_comp_ti | (intros; apply GlobalTheory.CompanionTheory.TiArch.isArchSmooth_comp_ti <;> assumption)
