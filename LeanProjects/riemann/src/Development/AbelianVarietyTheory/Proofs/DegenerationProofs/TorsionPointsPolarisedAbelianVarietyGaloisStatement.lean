import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPointsPolarisedAbelianVarietyGalois
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_points_polarised_abelianVariety_galois : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ), l.Prime → (∀ n, Nat.card {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l ^ n = 1} = l ^ (n * (2 * P.g))) ∧ (∃ e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ, ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ ∀ (τ : Ω ≃ₐ[K] Ω) n (x y x' y' : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l ^ n = 1 → y ^ l ^ n = 1 → x'.left = spMap τ.toRingEquiv.toRingHom ≫ x.left → y'.left = spMap τ.toRingEquiv.toRingHom ≫ y.left → (e n x y : Ω) ^ l ^ n = 1 ∧ (e n x' y' : Ω) = τ (e n x y)) ∧ ((∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ n, ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ Normal K L ∧ IsPGroup l (L ≃ₐ[K] L) ∧ ∀ x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A), x ^ l ^ n = 1 → ∃ y : Sp L ⟶ P.A.left, spMap (algebraMap L Ω) ≫ y = x.left) := by
  first | exact @GlobalTheory.torsion_points_galois_module | exact GlobalTheory.torsion_points_galois_module | (intros; apply GlobalTheory.torsion_points_galois_module <;> assumption)
