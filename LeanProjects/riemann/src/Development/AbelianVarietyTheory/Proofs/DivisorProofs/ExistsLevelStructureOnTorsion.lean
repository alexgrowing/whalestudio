import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionBySetPowOfDivisibleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_structure_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ j : ℕ, ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ o.A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  first | (exact @GlobalTheory.QuotientCardinalityFinrank.torsion_points_free) | (exact GlobalTheory.QuotientCardinalityFinrank.torsion_points_free) | (intros; apply GlobalTheory.QuotientCardinalityFinrank.torsion_points_free  <;> assumption)
