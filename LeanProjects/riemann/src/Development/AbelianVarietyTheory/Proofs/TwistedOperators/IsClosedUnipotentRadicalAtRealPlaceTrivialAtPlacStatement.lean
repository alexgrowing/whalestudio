import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedUnipotentRadicalAtRealPlaceTrivialAtPlac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_unipotentRadical_atRealPlace_trivialAtPlace : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau), IsClosed (GlobalTheory.FibreAtTau.atP θ V C τ : Set (NI V C)) ∧ IsClosed (GlobalTheory.FibreAtTau.offP θ V C τ : Set (NI V C)) := by
  first | exact @GlobalTheory.FibreAtTau.isClosed_atP_and_isClosed_offP | exact GlobalTheory.FibreAtTau.isClosed_atP_and_isClosed_offP | (intros; apply GlobalTheory.FibreAtTau.isClosed_atP_and_isClosed_offP <;> assumption)
