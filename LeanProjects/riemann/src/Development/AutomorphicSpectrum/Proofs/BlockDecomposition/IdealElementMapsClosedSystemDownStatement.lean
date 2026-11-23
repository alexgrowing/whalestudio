import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDown
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistSmulHomApp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeIffAffineSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_element_maps_closed_system_down : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ a ∈ I, MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | exact GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | (intros; apply GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions <;> assumption)
