import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisActionTorsionPairingTameFixedPoints
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
theorem _root_.GlobalTheory.T.galois_action_torsion_pairing_tame_fixedPoints : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l q : ℕ), l.Prime → (∀ (τ : Ω ≃ₐ[K] Ω) (x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), x ^ l = 1 → spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left) → ∀ (σ φ : Ω ≃ₐ[K] Ω) (K' : Type) [Field K'] (j : K' →+* Ω), (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) → (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → x ∈ j.fieldRange)) → ∃ (e : ℕ → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) → Ωˣ) (act : (Ω ≃ₐ[K] Ω) →* MulAut (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A)), (∀ τ x, (act τ x).left = spMap τ.toRingEquiv.toRingHom ≫ x.left) ∧ ((∀ n x x' y, x ^ l ^ n = 1 → x' ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (x * x') y = e n x y * e n x' y ∧ e n y x = (e n x y)⁻¹) ∧ (∀ n x y, x ^ l ^ (n + 1) = 1 → y ^ l ^ n = 1 → e (n + 1) x y = e n (x ^ l) y) ∧ (∀ n x, x ^ l ^ n = 1 → (∀ y, y ^ l ^ n = 1 → e n x y = 1) → x = 1)) ∧ (∀ N n x y, x ^ l ^ n = 1 → y ^ l ^ n = 1 → e n (act σ x) (act σ y) = e n x y ∧ e n (act (φ ^ N) x) (act (φ ^ N) y) = e n x y ^ (q ^ N)) ∧ (∀ N n x, x ^ l ^ n = 1 → act (φ ^ N) (act σ x) = (act σ)^[q ^ N] (act (φ ^ N) x)) ∧ ∀ n x, x ^ l ^ n = 1 → act σ x = x → ∃ y : Sp K' ⟶ P.A.left, spMap j ≫ y = x.left := by
  first | exact @GlobalTheory.SS.galois_action_torsion_points | exact GlobalTheory.SS.galois_action_torsion_points | (intros; apply GlobalTheory.SS.galois_action_torsion_points <;> assumption)
