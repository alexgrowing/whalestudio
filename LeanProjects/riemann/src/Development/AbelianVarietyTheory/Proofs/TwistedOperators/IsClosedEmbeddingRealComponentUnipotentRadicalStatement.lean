import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClosedEmbeddingRealComponentUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedEmbedding_realComponent_unipotentRadical : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∀ E : GA D V →* Formalism.REAL.UJ (M.ε τ), (∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) → ∃ W : Submodule ℂ (Fin V.rank → ℂ), GlobalTheory.Dec.IsIsoC (M.ε τ) W ∧ Topology.IsClosedEmbedding (fun p : GlobalTheory.FibreAtTau.atP θ V C τ => E ((p : NI V C) : GA D V)) ∧ Set.range (fun p : GlobalTheory.FibreAtTau.atP θ V C τ => E ((p : NI V C) : GA D V)) = GlobalTheory.Dec.NW (M.ε τ) W := by
  first | exact @GlobalTheory.FibreAtTauEmb.isClosedEmbedding_atP | exact GlobalTheory.FibreAtTauEmb.isClosedEmbedding_atP | (intros; apply GlobalTheory.FibreAtTauEmb.isClosedEmbedding_atP <;> assumption)
