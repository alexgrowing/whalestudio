import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierRestrictIffCartierAt
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.effCartier_restrict_iff_cartier_at : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (O : X.Opens), FinalTheorems.EffCartier (J.comap O.ι) ↔ ∀ x ∈ O, CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.effCartier_comap_opens_iff <;> assumption)
