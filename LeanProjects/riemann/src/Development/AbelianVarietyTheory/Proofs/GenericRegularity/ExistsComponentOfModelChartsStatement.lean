import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsComponentOfModelCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_of_modelCharts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp), ∃ Z : Comp Xo c, ∀ (x : (U.X k).dom) (C : FChart h) (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap ψ C.y z → FrBor t z (U.un k x) → C.Z = Z := by
  first | exact @GlobalTheory.OneComp.exists_comp_of_charts | exact GlobalTheory.OneComp.exists_comp_of_charts | (intros; apply GlobalTheory.OneComp.exists_comp_of_charts <;> assumption)
