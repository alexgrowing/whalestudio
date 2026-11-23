import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionKilledByIdealCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.card_torsion_killed_by_ideal_char_zero : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w : Ideal (𝓞 D.F)), w ≠ ⊥ → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] [CharZero κ] (x : Sp κ ⟶ S), Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * D.n) := by
  first | exact @GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero | exact GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero | (intros; apply GlobalTheory.UPel.HT.ES.CharZeroCount.card_killedBy_charZero <;> assumption)
