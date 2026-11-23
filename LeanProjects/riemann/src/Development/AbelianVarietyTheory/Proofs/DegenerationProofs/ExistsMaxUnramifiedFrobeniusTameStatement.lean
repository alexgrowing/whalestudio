import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMaxUnramifiedFrobeniusTame
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
theorem _root_.GlobalTheory.T.exists_maxUnramified_frobenius_tame_alt : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ (l : ℕ), l.Prime → IsUnit (l : V) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] (q : ℕ), q = Nat.card (IsLocalRing.ResidueField V) → ∃ (R : Subalgebra V Ω) (_ : IsLocalRing R) (σ φ : Ω ≃ₐ[K] Ω), SH R (FractionRing R) ∧ IsLocalHom (algebraMap V R) ∧ (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ (q ^ m) = c) ∧ (∀ s : Finset R, ∃ (W : Subalgebra V R) (_ : IsDiscreteValuationRing W), (↑s : Set R) ⊆ W ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Module.Finite V W ∧ IsLocalHom W.val.toRingHom ∧ ∃ f, 1 ≤ f ∧ ∀ x ∈ W, (φ ^ f) ((x : R) : Ω) = x) ∧ (∀ x ∈ R, σ x = x) ∧ (∀ x : R, ∃ y : R, (y : Ω) = φ x ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → σ ζ = ζ ∧ φ ζ = ζ ^ q) ∧ ∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∀ x ∈ L, φ (σ x) = (σ ^ q) (φ x) ∧ (σ x = x → ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) := by
  first | exact @GlobalTheory.SS.exists_maxUnramified_frobenius_tame | exact GlobalTheory.SS.exists_maxUnramified_frobenius_tame | (intros; apply GlobalTheory.SS.exists_maxUnramified_frobenius_tame <;> assumption)
