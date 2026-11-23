import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegerConjPrescribedResiduesPlaces
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LamHomApply
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_conj_prescribed_residues_places : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (b : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Formalism.L2.DIV.kP PP), ∃ c : 𝓞 D.host.E, ∀ PP ∈ P, Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar c) = b PP := by
  first | exact @GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | exact GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places | (intros; apply GlobalTheory.SW.Lev.exists_bar_mk_eq_at_places <;> assumption)
