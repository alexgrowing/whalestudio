import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabelling
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twisted_simplicial_star_label : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab w ψ' : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 lab → SimpLab bar q φ lab → IsTwG w0 w → IsCentreSet bar q φ w →
    IsPolyFan bar q ψ' → Subordinate bar q ψ' φ → IsStarOf bar q φ w ψ' →
    ∃ lab' : InvFun O, IsTwG w0 lab' ∧ SimpLab bar q ψ' lab' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star | exact GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star <;> assumption)
