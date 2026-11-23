import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3

namespace UpperTheory.Gal.crystallineComparison.Br

theorem trPush : TrPush := by
  intro l _ B Z Y p q s hs n tr htr W x m σ hσ hiso z
  exact htr W (x ≫ p) x rfl (Fin m) σ (fun j => by rw [← hs, ← Category.assoc, hσ j]) ⟨hσ, hiso⟩ z

end UpperTheory.Gal.crystallineComparison.Br
