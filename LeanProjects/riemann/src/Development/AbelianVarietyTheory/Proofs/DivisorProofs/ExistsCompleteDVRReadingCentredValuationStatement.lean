import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDVRReadingCentredValuation
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
theorem _root_.GlobalTheory.T.exists_completeDVR_reading_centredValuation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (ν : Valuation R (WithZero (Multiplicative ℤ))), (∀ a, ν a ≤ 1) → (∀ a ∈ IsLocalRing.maximalIdeal R, ν a < 1) → (∀ a, ν a = 0 → a = 0) → ∃ (T : Formalism.L2.Pj.CDVR) (g : R →+* T.V) (ρ : ℝ), 0 < ρ ∧ Function.Injective g ∧ (∀ a ∈ IsLocalRing.maximalIdeal R, g a ∈ IsLocalRing.maximalIdeal T.V) ∧ ∀ a, ν a ≠ 0 → -((WithZero.log (ν a) : ℤ) : ℝ) = ρ * (Formalism.L2.Pj.vV T.V (algebraMap T.V T.Fr (g a)) : ℝ) := by
  first | exact @GlobalTheory.CentredDiscreteRead.exists_cdvr_read | exact GlobalTheory.CentredDiscreteRead.exists_cdvr_read | (intros; apply GlobalTheory.CentredDiscreteRead.exists_cdvr_read <;> assumption)
