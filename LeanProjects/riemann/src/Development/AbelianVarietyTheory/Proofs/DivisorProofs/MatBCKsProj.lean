import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised

noncomputable section

namespace GlobalTheory.KS.Leray

open AlgebraicGeometry CategoryTheory Limits

def fibMap {X Y T : Scheme.{0}} (f : Y ⟶ X) (x : T ⟶ X) (u : Y ⟶ Y) (hu : u ≫ f = f) : pullback f x ⟶ pullback f x :=
  pullback.map f x f x u (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hu]) (by simp)

variable {S B B' : Scheme.{0}}

def ksProj (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : ksBC A m p b ⟶ pullback p b :=
  pullback.map _ _ _ _ (pow A m).hom (𝟙 _) (𝟙 _) (by simp) (by simp)

end GlobalTheory.KS.Leray
