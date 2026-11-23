import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRanksDegreesAddWithMassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsSupLatticeSplitOverComponentsStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.Proof.componentDegrees_sum_le_total_degree

theorem degOn_sum_le : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  intro D H Dw l Xo c r U V dict hc G hG
  haveI : Finite (Comp Xo c) := finite_comp
  have hS : Splits U G := GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict (fun σ hσ => (hc.2 σ hσ).1) G
  have hO := GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hc G
  have hA : Adds U V dict G := GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G hS hO.1
  obtain ⟨-, hr, -, -, hd⟩ := hA.2 hG
  refine ⟨hr, ?_⟩
  rw [hd]
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun Z _ => ?_
  have hlog : (∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) ≤ 0 :=
    Finset.sum_nonpos fun σ _ => Real.log_nonpos (hO.2.1 Z σ).1 (hO.2.1 Z σ).2
  have hq : ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg _)
  have hk : (0:ℝ) ≤ (rankOn U Z G : ℝ) / 2 := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hq]

end GlobalTheory.Proof.componentDegrees_sum_le_total_degree
