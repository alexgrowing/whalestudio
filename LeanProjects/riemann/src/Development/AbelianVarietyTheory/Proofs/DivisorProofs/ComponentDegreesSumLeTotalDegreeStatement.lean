import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentDegrees_sum_le_total_degree : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  first | exact @GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | exact GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le | (intros; apply GlobalTheory.Proof.componentDegrees_sum_le_total_degree.degOn_sum_le <;> assumption)
