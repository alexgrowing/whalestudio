import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymplecticLevelOfPulledBackObject
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymplecticLevel_of_pulledBack_object : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ)
  (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
  (o' : Obj b N (T.hom ≫ t)) (m : ObjMap o' o T.hom)
  (lv' : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T.left) ⟶ o'.A)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)),
    (∀ a, (lv' a).left ≫ m.φ = (lv a).left) → SympCond o h M T t₁ lv →
      IsSympLev o'.P h M (zetaAway M) t₁ lv' := by
  first | exact @GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | exact GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull | (intros; apply GlobalTheory.HTSympCover.isSympLev_of_sympCond_pull <;> assumption)
