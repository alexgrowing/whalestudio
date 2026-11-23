import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothLocalRingFreeDifferentials
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_local_ring_free_differentials : ∀ (K : Type) [Field K] (D : ℕ) (Y : Scheme.{0}) (g : Y ⟶ Sp K), SmoothOfRelativeDimension D g → ∀ (U : Y.affineOpens) (P : Ideal Γ(Y, U.1)) [P.IsPrime], letI := secAlgebra g U.1; Algebra.FinitePresentation K Γ(Y, U.1) ∧ Module.Free (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.Finite (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] ∧ Module.finrank (Localization.AtPrime P) Ω[Localization.AtPrime P⁄K] = D := by
  first | exact @GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | exact GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime | (intros; apply GlobalTheory.CompanionTheory.ResKCoords.finitePresentation_and_kaehler_atPrime <;> assumption)
