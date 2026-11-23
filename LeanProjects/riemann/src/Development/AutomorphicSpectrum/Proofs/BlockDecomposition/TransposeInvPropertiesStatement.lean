import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInvProperties
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transposeInv_properties : (∀ (R : Type) [CommRing R] (n : ℕ) (g h : GL (Fin n) R), ti (g * h) = ti g * ti h ∧ ti (ti g) = g) ∧
  (∀ γ : GL (Fin 3) ℚ, ti (dia γ) = dia (ti γ)) ∧ (∀ γ : GL (Fin 2) ℚ, ti (dia2 γ) = dia2 (ti γ)) ∧
  Continuous (ti : G3 → G3) ∧ Continuous (ti : G2 → G2) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg | exact GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg | (intros; apply GlobalTheory.CompanionTheory.UnfoldingAlt.Ti.ti_alg <;> assumption)
