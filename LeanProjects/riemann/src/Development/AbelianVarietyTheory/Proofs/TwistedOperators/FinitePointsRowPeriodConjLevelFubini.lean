import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarTraceConjEqConstMulKernelImageStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirectStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.CellMass

theorem cell_fubini : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ j ∈ idx D,
    ∀ ρ : Measure ((rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))), ρ.IsHaarMeasure →
    ∃ (κ : ℝ) (la : Measure ((rowN ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))))) (ν : Measure (GfC (ch.G.V (.top j)))),
      0 < κ ∧ la.IsHaarMeasure ∧ ν.IsHaarMeasure ∧ ∀ b : GfC (ch.G.V (.grid D.R.m j)),
        ρ.real {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} =
          κ * la.real {n | b⁻¹ * n.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} * ν.real (prSet ch.G j b) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ => ?_⟩⟩
  intro j hj ρ hρ
  obtain ⟨-, -, -, h4, h5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.grid D.R.m j))
  obtain ⟨-, -, -, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V (.top j))
  obtain ⟨c1, c2, c3, c4, c5, π, σ, hπ, hσ, hπσ, hker, hpr⟩ := GlobalTheory.T.rowPeriodSubgroup_finitePoints_semidirect ch j hj
  obtain ⟨κ, la, ν, hκ, hla, hν, h⟩ := GlobalTheory.T.haar_trace_conj_eq_const_mul_kernel_image _ _ _ π σ c1 c2 c3 c4 c5 hπ hσ hπσ hker ρ hρ
  exact ⟨κ, la, ν, hκ, hla, hν, fun b => by rw [hpr b]; exact h b⟩

end GlobalTheory.CellMass
