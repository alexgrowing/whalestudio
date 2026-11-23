import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableFlagSpaceAtlas
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.FlagChartsCoverFramedFieldPoints
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.Reg
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_flagSpace_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (h : GenFrEx Xo c), ∃ (ι : Type) (_ : Countable ι) (C : ι → FChart h), ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L), ∃ (i : ι) (ψ : (C i).R →ₐ[c.F] L) (z : FrPt Xo c L) (t : Ix Dw → Lˣ), FrMap ψ (C i).y z ∧ FrBor t z y := by
  first | exact @GlobalTheory.Reg.exists_countable_atlas | exact GlobalTheory.Reg.exists_countable_atlas | (intros; apply GlobalTheory.Reg.exists_countable_atlas <;> assumption)
