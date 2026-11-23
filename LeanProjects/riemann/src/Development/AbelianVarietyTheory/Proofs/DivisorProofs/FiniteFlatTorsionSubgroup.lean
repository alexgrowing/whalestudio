import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPowPFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_torsion_subgroup : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  first | (exact @GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (exact GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (intros; apply GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow  <;> assumption)
