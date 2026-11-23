import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

noncomputable section
namespace GlobalTheory.RSPole

def schurDir (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∑' l : {l : Fin n → ℕ // Antitone l},
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)))

def eulD {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ∏' w, schurDir (q w) (α w) x

def thetaZ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a)) (𝓕 : Set (GA E a))
    (ℓ : Fin a) (φ φ' : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (x : ℝ) : ℂ :=
  ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ φ' Φ J η g
      ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
    ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ

example (x : ℝ) : eulD (I := Empty) (fun _ => 2) (n := 1) (fun _ _ => 1) x = 1 := by simp [eulD]

end GlobalTheory.RSPole
