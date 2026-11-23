import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelTwistBySimilitude
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticLevel_twist_by_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (T : Over S) (t₁ : T.left ⟶ Sp (cycAway M))
    (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)), SympCond o h M T t₁ lv →
    ∀ (a : sympSimGrp h M) (n : ℕ) (σ : cycAway M →+* cycAway M), IsMultOf a n →
      σ (zetaAway M) = zetaAway M ^ n → SympCond o h M T (t₁ ≫ spMap σ) (sympTwist a lv) := by
  first | exact @GlobalTheory.HTSympCover.sympCond_twist | exact GlobalTheory.HTSympCover.sympCond_twist | (intros; apply GlobalTheory.HTSympCover.sympCond_twist <;> assumption)
