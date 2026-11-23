import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.BlockTheory.AbelianSchemeLaw.SemiAbelianSchemes
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.l_power_torsion_endomorphism_evaluation : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly f := by
  first | (exact @GlobalTheory.AV.AbVar.charpoly_eq_lattice_model) | (exact GlobalTheory.AV.AbVar.charpoly_eq_lattice_model) | (intros; apply GlobalTheory.AV.AbVar.charpoly_eq_lattice_model  <;> assumption)
