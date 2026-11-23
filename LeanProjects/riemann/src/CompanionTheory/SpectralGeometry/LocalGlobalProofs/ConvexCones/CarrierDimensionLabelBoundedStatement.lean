import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CarrierDimensionLabelBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_dimension_label_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O), CMOrd O bar → ∀ (q : ℕ) (ψ lab : InvFun O), IsCarrierDim bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded | exact GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.IntegerFinrankMultiplicativity.carrierDim_bounded <;> assumption)
