import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toroidal_flag_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  first | exact @GlobalTheory.CompanionTheory.FlagSmooth.smooth_proj_flagStr | exact GlobalTheory.CompanionTheory.FlagSmooth.smooth_proj_flagStr | (intros; apply GlobalTheory.CompanionTheory.FlagSmooth.smooth_proj_flagStr <;> assumption)
