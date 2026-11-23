import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.Iwasawa

theorem exists_mul_of_rank (D : D7) (A : HSp D) (g : GlobalTheory.StdUnn.G D A.rank) :
    ∃ p ∈ GlobalTheory.StdUnn.P D A.rank, ∃ k ∈ GlobalTheory.StdUnn.K D A.rank, g = p * k := by
  obtain ⟨μ, hμ, hconj⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨a, ha⟩ := GlobalTheory.Doubling.exists_isMaj A
  obtain ⟨p, hp⟩ := hconj A a ha κ hκ
  obtain ⟨q, k, hk, hqk⟩ := (GlobalTheory.Eis.isIwasawa_Khat (GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha)).1
    (κ.symm g * (p : GA D (dblSp A))⁻¹)
  refine ⟨κ ((q : GA D (dblSp A)) * p), ?_, κ ((p : GA D (dblSp A))⁻¹ * k * p), (hp k).1 hk, ?_⟩
  · exact (GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ _).1 (Subgroup.mul_mem _ q.2 p.2)
  · have h1 : κ.symm g = (q : GA D (dblSp A)) * k * p := by
      rw [← hqk, inv_mul_cancel_right]
    have h2 : (q : GA D (dblSp A)) * p * ((p : GA D (dblSp A))⁻¹ * k * p) = (q : GA D (dblSp A)) * k * p := by
      group
    rw [← map_mul, h2, ← h1, MulEquiv.apply_symm_apply]

theorem exists_mul : ∀ (D : D7) (n : ℕ) (g : GlobalTheory.StdUnn.G D n),
    ∃ p ∈ GlobalTheory.StdUnn.P D n, ∃ k ∈ GlobalTheory.StdUnn.K D n, g = p * k :=
  fun D n g => exists_mul_of_rank D (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral n) g

end GlobalTheory.StdUnn.Iwasawa
