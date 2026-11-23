import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoPullbackMapOfFlat
import Mathlib

open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mono_pullback_map_of_flat' : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [Flat f] (G G' : Y.Modules) (φ : G ⟶ G') [Mono φ], Mono ((Scheme.Modules.pullback f).map φ) := by
  first | exact @GlobalTheory.mono_pullback_map_of_flat | exact GlobalTheory.mono_pullback_map_of_flat | (intros; apply GlobalTheory.mono_pullback_map_of_flat <;> assumption)
