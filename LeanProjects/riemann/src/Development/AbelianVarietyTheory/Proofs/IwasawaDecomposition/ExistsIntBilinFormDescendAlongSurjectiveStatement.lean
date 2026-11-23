import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntBilinFormDescendAlongSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intBilinForm_descend_along_surjective : ∀ {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y), Function.Surjective f → ∀ β : LinearMap.BilinForm ℤ X,
  (∀ x, f x = 0 → ∀ y, β x y = 0) → (∀ x, f x = 0 → ∀ y, β y x = 0) →
  ∃ ζ : LinearMap.BilinForm ℤ Y, ∀ x y, ζ (f x) (f y) = β x y := by
  first | exact @GlobalTheory.exists_bilinForm_descend_of_surjective | exact GlobalTheory.exists_bilinForm_descend_of_surjective | (intros; apply GlobalTheory.exists_bilinForm_descend_of_surjective <;> assumption)
