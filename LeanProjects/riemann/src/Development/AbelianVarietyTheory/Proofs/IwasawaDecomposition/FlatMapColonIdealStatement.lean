import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_map_colon_ideal : ∀ {A R : Type} [CommRing A] [IsNoetherianRing A] [CommRing R] (φ : A →+* R), φ.Flat → ∀ I J : Ideal A, (I.colon J).map φ = (I.map φ).colon (J.map φ) := by
  first | exact @GlobalTheory.ideal_map_colon_eq_of_flat | exact GlobalTheory.ideal_map_colon_eq_of_flat | (intros; apply GlobalTheory.ideal_map_colon_eq_of_flat <;> assumption)
