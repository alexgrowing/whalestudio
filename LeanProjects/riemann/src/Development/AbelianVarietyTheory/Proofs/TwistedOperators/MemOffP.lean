import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FibreAtTau

variable {D : D7} (θ : InfFam D) (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (τ : D.what₂.Tau)

def atP : Subgroup (NI V C) :=
  (GinfC V ⊓ ⨅ (τ' : D.what₂.Tau) (_ : τ' ≠ τ), (GlobalTheory.RowReal.infMatHom V (θ τ')).ker).subgroupOf (NI V C)

def offP : Subgroup (NI V C) := ((GlobalTheory.RowReal.infMatHom V (θ τ)).ker).subgroupOf (NI V C)

variable {θ V C τ}

theorem mem_atP {p : NI V C} :
    p ∈ atP θ V C τ ↔ (p : GA D V) ∈ GinfC V ∧ ∀ τ', τ' ≠ τ → cmp θ τ' (p : GA D V) = 1 := by
  simp only [atP, Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl

theorem mem_offP {q : NI V C} : q ∈ offP θ V C τ ↔ cmp θ τ (q : GA D V) = 1 := by
  simp only [offP, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  rfl

end GlobalTheory.FibreAtTau
