import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (exact GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (intros; apply GlobalTheory.UPel.HT.ES.IsogRep.exists_rep  <;> assumption)
