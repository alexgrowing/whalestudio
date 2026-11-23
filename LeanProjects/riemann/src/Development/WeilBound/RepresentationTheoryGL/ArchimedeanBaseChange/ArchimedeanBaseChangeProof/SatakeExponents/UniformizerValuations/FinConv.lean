import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace PositivityTheory.Rg.BcB.FC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

abbrev Fam (E : Type) [Field E] [NumberField E] (a b : ℕ) : Type := ∀ w : Pl E, GLw a w × GLw b w → ℂ

def cvL (φ ψ : Fam E a b) : Fam E a b := fun w y => hint (K2 a b w) fun z => φ w z * ψ w (z⁻¹ * y)

def adL (φ : Fam E a b) : Fam E a b := fun w y => starRingEnd ℂ (φ w y⁻¹)

def szL (w : Pl E) (g : GLw n w) : ℝ :=
  Real.posLog (⨆ p : Fin n × Fin n, ‖g.val p.1 p.2‖) + Real.posLog (⨆ p : Fin n × Fin n, ‖(g⁻¹ : GLw n w).val p.1 p.2‖)

theorem adL_adL (φ : Fam E a b) : adL (adL φ) = φ := by
  funext w y
  simp [adL]

def FamCl : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (φ ψ : Fam E a b), IsTestP φ →
  IsTestP ψ → IsTestP (cvL φ ψ) ∧ IsTestP (adL φ)

def FinTest : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ φ₁ φ₂ : Fam E a b, IsTestP φ₁ → IsTestP φ₂ → Continuous (finFn S φ₁ φ₂) ∧ HasCompactSupport (finFn S φ₁ φ₂) ∧
    ∃ U : Subgroup (Gf E a b), IsOpen (U : Set (Gf E a b)) ∧ IsCompact (U : Set (Gf E a b)) ∧
      ∀ u ∈ U, ∀ y, finFn S φ₁ φ₂ (u * y) = finFn S φ₁ φ₂ y ∧ finFn S φ₁ φ₂ (y * u) = finFn S φ₁ φ₂ y

def FinConv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ [MeasurableSpace (Gf E a b)] [BorelSpace (Gf E a b)] (ν : Measure (Gf E a b)) [ν.IsHaarMeasure]
    (φ₁ φ₂ ψ₁ ψ₂ : Fam E a b), IsTestP φ₁ → IsTestP φ₂ → IsTestP ψ₁ → IsTestP ψ₂ → ∀ g,
    ∫ h, finFn S φ₁ φ₂ h * finFn S ψ₁ ψ₂ (h⁻¹ * g) ∂ν =
      ((ν (((Kf E a).prod (Kf E b) : Subgroup (Gf E a b)) : Set (Gf E a b))).toReal : ℂ) *
        finFn S (cvL φ₁ ψ₁) (cvL φ₂ ψ₂) g

def FinAdj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (S : Set (Pl E)) (φ₁ φ₂ : Fam E a b)
  (y : Gf E a b), IsTestP φ₁ → IsTestP φ₂ → starRingEnd ℂ (finFn S φ₁ φ₂ y⁻¹) = finFn S (adL φ₁) (adL φ₂) y

def FinSize : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ (φ₁ φ₂ : Fam E a b) (T : Finset (Pl E)) (r₁ r₂ : Pl E → ℝ), IsTestP φ₁ → IsTestP φ₂ →
    (∀ w, 0 ≤ r₁ w ∧ 0 ≤ r₂ w) → (∀ w, w ∉ T → r₁ w = 0 ∧ r₂ w = 0) →
    (∀ w ∈ S, ∀ y, φ₁ w y ≠ 0 → szL w y.1 ≤ r₁ w ∧ szL w y.2 ≤ r₁ w) →
    (∀ w ∈ S, IsSplitAt w → ∀ y, φ₂ w y ≠ 0 → szL w y.1 ≤ r₂ w ∧ szL w y.2 ≤ r₂ w) →
    ∀ y, finFn S φ₁ φ₂ y ≠ 0 → logSize (finGL E a y.1) ≤ ∑ w ∈ T, (r₁ w + r₂ w) ∧
      logSize (finGL E b y.2) ≤ ∑ w ∈ T, (r₁ w + r₂ w)

def SzConv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
  (∀ g h : GLw n w, szL w (g * h) ≤ szL w g + szL w h) ∧ (∀ g : GLw n w, szL w g⁻¹ = szL w g) ∧
    (∀ g ∈ GlobalTheory.LFun.KGL w n, szL w g = 0) ∧ ∀ C : Set (GLw n w), IsCompact C → ∃ r, ∀ g ∈ C, szL w g ≤ r

end PositivityTheory.Rg.BcB.FC

end
