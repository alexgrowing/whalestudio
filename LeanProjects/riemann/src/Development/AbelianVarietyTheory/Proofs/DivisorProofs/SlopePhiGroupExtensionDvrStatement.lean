import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopePhiGroupExtensionDvr
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slope_phi_group_extension_dvr : Hypotheses2 → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Formalism.L2.Pj.CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (φ : ℝ), GlobalTheory.SlopeRec.HasPhi y φ → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))), (IsLocalRing.closedPoint T.V : Sp T.V) ∉ abLocus G.G → 0 < φ := by
  first | exact @GlobalTheory.PeriodMinPos.phi_pos | exact GlobalTheory.PeriodMinPos.phi_pos | (intros; apply GlobalTheory.PeriodMinPos.phi_pos <;> assumption)
