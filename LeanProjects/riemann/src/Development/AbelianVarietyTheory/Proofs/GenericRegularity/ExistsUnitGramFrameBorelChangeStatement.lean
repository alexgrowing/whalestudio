import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_gram_frame_borel_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → (∀ k (x : (U.X k).dom), ∃ x' : (U.X k).dom, IsUnitFr (U.X k) x'.1 ∧ (∃ b ∈ FD.Bor (U.X k).Ψ r, x'.1 = FD.rmul x.1 b) ∧ (∃ t : Ix Dw → (CAt σ)ˣ, FrBor t (U.un k x') (U.un k x)) ∧ ∀ (la : FD.Wt (U.X k).Ψ r) (P : FD.Frame (U.X k).Ψ r → ℂ), (U.X k).IsSec la P → (U.X k).pnorm la P x.1 = ‖P x'.1‖) ∧ ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 ∧ FrBor t (U.un k x) y := by
  first | exact @GlobalTheory.FrameNorm.exists_unitFr_frBor | exact GlobalTheory.FrameNorm.exists_unitFr_frBor | (intros; apply GlobalTheory.FrameNorm.exists_unitFr_frBor <;> assumption)
