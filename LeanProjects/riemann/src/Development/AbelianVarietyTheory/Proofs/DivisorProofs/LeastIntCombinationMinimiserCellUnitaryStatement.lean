import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeastIntCombinationMinimiserCellUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.least_intCombination_minimiserCell_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ : InvFun (𝓞 E)), IsPolFan H.bar q φ → ∀ (N : ℕ) [NeZero N], 3 ≤ N → Odd N → ∃ (B ι : ℕ) (𝓛 : ∀ n : ℕ, Finset (Finset ((Fin n → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (n : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (eb : X ≃ₗ[ℤ] (Fin n → ℤ)), n < B ∧ ∀ (b : LinearMap.BilinForm ℤ X), b ∈ balForms H.bar X → (∀ y, y ≠ 0 → 0 < b y y) → ∀ μ : (Fin n → ZMod N) → X, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → ∃ L ∈ 𝓛 n, ∀ b' : LinearMap.BilinForm ℤ X, b' ∈ balForms H.bar X → (∀ y, 0 ≤ b' y y) → (∀ cl (α : X), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b' (μ cl) (μ cl) ≤ b' α α) → (∀ ν ∈ L, (ι : ℝ) * φ.evalZ b' ≤ ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl)) ∧ ∃ ν ∈ L, (ι : ℝ) * φ.evalZ b' = ∑ cl, (ν cl : ℝ) * b' (μ cl) (μ cl) := by
  first | exact @GlobalTheory.UPoinc.finite_types_unitary | exact GlobalTheory.UPoinc.finite_types_unitary | (intros; apply GlobalTheory.UPoinc.finite_types_unitary <;> assumption)
