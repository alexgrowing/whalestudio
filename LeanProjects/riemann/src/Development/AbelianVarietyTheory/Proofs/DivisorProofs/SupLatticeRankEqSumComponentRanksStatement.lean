import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupLatticeRankEqSumComponentRanks
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponents
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supLattice_rank_eq_sum_component_ranks : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (G : WTZ D.host.E), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → GoodW U x V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G := by
  first | exact @GlobalTheory.RankAdd.rankW_eq_finsum_rankOn | exact GlobalTheory.RankAdd.rankW_eq_finsum_rankOn | (intros; apply GlobalTheory.RankAdd.rankW_eq_finsum_rankOn <;> assumption)
