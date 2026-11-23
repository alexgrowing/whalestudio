import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmooth
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EffCartierIffForallCartAt
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocPrincipalSpan
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_finite_projective_of_smooth : ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth → ((Ideal.Quotient.mk I).comp φ).Smooth → Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | exact GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent <;> assumption)
