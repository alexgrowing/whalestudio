import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralHeckeElementExists
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_hecke_element_exists : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank) (PP : Pl D.host.E), IsBaseFrame V β Λ N → ((N : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal → (∀ P', P' ∈ L.Pg ∨ P' ∈ L.Q → P' ≠ PP ∧ ¬ IsConjPl P' PP) → Bridge.SplitOff PP ∅ → ∃ z : GA D V, (∀ g, Commute z g) ∧ IsHeckeAt V PP V.rank z ∧ ∀ k ≤ V.rank, ∃ (α : GA D V) (R R' : Finset (GA D V)), IsHeckeAt V PP k α ∧ IsHeckeAt V PP (V.rank - k) (z * α⁻¹) ∧ Bridge.IsDC (levG V β L) α⁻¹ R ∧ Bridge.IsDC (levG V β L) α R' ∧ R.card = R'.card := by
  first | exact @GlobalTheory.HeckeCompl.central_and_complement | exact GlobalTheory.HeckeCompl.central_and_complement | (intros; apply GlobalTheory.HeckeCompl.central_and_complement <;> assumption)
