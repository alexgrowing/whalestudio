import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.CorrQF

def IsogTarget {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    (M : Model b N) (c : ℕ) {L : Type} [Field L] (ξ ζ : Sp L ⟶ M.X) : Prop :=
  ξ ≫ M.s = ζ ≫ M.s ∧ ∃ (o o' : Obj b N (ξ ≫ M.s)) (ψ : o.A ⟶ o'.A),
    Nonempty (ObjMap o M.univ ξ) ∧ Nonempty (ObjMap o' M.univ ζ) ∧ IsPIsog c o o' ψ

end GlobalTheory.UPel.HT.ES.CorrQF
