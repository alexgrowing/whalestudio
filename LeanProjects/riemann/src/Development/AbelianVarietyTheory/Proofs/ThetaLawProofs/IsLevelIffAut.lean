import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KaRuleK
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.SimilTheta
open Matrix

variable {g : ℕ}

def lat (τ : Matrix (Fin g) (Fin g) ℂ) (k n : Fin g → ℤ) : Fin g → ℂ :=
  (fun i => (k i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))

def aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (k i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
    ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z))

def tors (τ : Matrix (Fin g) (Fin g) ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ) (k n : Fin 4 → Fin g → ℤ) (r : Fin 4) :
    Fin g → ℂ := (m : ℂ)⁻¹ • ∑ c, al r c • lat τ (k c) (n c)

def simTheta (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (m : ℕ)
    (k n : Fin 4 → Fin g → ℤ) (y : Fin 4 → Fin g → ℂ) : ℂ :=
  (∏ r, thetaChar τ a b (∑ c, al r c • y c + tors τ al m k n r)) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.aut_ne_zero (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (k n : Fin g → ℤ) (z : Fin g → ℂ) :
    _root_.GlobalTheory.SimilTheta.aut τ a b k n z ≠ 0 :=
  Complex.exp_ne_zero _

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.isLevel_iff_aut (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ) (F : (Fin g → ℂ) → ℂ) :
    _root_.GlobalTheory.KeyKa.IsLevel τ a b l F ↔ Differentiable ℂ F ∧ ∀ k n z, F (z + _root_.GlobalTheory.SimilTheta.lat τ k n) = _root_.GlobalTheory.SimilTheta.aut τ a b k n z ^ l * F z :=
  Iff.rfl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_add (τ : Matrix (Fin g) (Fin g) ℂ) (k n k' n' : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (k + k') (n + n') = _root_.GlobalTheory.SimilTheta.lat τ k n + _root_.GlobalTheory.SimilTheta.lat τ k' n' := by
  have h : (fun i => ((n + n') i : ℂ)) = (fun i => (n i : ℂ)) + fun i => (n' i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_add]
  ext i
  simp only [Pi.add_apply, Int.cast_add]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_zsmul (τ : Matrix (Fin g) (Fin g) ℂ) (s : ℤ) (k n : Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (s • k) (s • n) = s • _root_.GlobalTheory.SimilTheta.lat τ k n := by
  have h : (fun i => ((s • n) i : ℂ)) = (s : ℂ) • fun i => (n i : ℂ) := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
private theorem lat_zero_zero (τ : Matrix (Fin g) (Fin g) ℂ) :
    _root_.GlobalTheory.SimilTheta.lat τ 0 0 = 0 := by
  have h : (fun i : Fin g => (((0 : Fin g → ℤ) i : ℤ) : ℂ)) = 0 := by
    ext i; simp
  unfold _root_.GlobalTheory.SimilTheta.lat
  rw [h, Matrix.mulVec_zero]
  ext i
  simp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory in
attribute [local instance] Over.cartesianMonoidalCategory in
open Matrix in
variable {g : ℕ} in
theorem _root_.GlobalTheory.SimilTheta.lat_sum (τ : Matrix (Fin g) (Fin g) ℂ) {K : Type} (s : Finset K) (k n : K → Fin g → ℤ) :
    _root_.GlobalTheory.SimilTheta.lat τ (∑ c ∈ s, k c) (∑ c ∈ s, n c) = ∑ c ∈ s, _root_.GlobalTheory.SimilTheta.lat τ (k c) (n c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lat_zero_zero τ
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, Finset.sum_insert hc, _root_.GlobalTheory.SimilTheta.lat_add, ih]

end GlobalTheory.SimilTheta
end
