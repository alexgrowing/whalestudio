import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaUnipotentActionCocycle
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_action_cocycle : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N, d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧ (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧ ∃ b : Fin d.ρ → AE D, actV B n d.fTop = vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  first | exact @GlobalTheory.HeisLaw.law | exact GlobalTheory.HeisLaw.law | (intros; apply GlobalTheory.HeisLaw.law <;> assumption)
