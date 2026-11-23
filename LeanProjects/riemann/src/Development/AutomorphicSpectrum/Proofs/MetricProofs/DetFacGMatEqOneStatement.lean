import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetFacGMatEqOne
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detFac_gMat_eq_one : ∀ (Ψ : Type) (p q : ℕ) (Ω : Type) [Field Ω] (τ : Ψ) (i : Fin (p + q)), detFac p i (gMat p q Ω τ) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.DetG.detFac_gMat <;> assumption)
