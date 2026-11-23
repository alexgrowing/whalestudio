import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrTransferQ

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC PositivityTheory.AutomorphicGaloisHodgeTate

namespace UpperTheory.Gal.TranscendenceTraces

theorem pullHQ_comp (l : ℕ) [Fact l.Prime] {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  rw [Functor.map_comp]
  simp only [pullHQ, pullHl_comp, LinearMap.baseChange_comp]

end UpperTheory.Gal.TranscendenceTraces

end
