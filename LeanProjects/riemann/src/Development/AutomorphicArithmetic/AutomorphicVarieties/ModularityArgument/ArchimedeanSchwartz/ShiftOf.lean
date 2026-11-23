import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Z.Inf

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def detAt (τ : K →+* ℂ) (x : Lie K n) : ℂ := coord τ (Matrix.of x).det

def nrm (x : Lie K n) : ℝ := ∏ w, ‖(Matrix.of x).det w‖ ^ 2

def wt (u : ℂ) (e : (K →+* ℂ) → ℕ) (x : Lie K n) : ℂ := ((nrm x : ℝ) : ℂ) ^ u * ∏ σ, (detAt σ x)⁻¹ ^ e σ

def pd (τ : K →+* ℂ) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F x (toL (single i j (atEmb τ 1))) - Complex.I * fderiv ℝ F x (toL (single i j (atEmb τ Complex.I))))

def rd (τ : K →+* ℂ) (i j : Fin n) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ F x (rmul (toL (single i j (atEmb τ 1))) x) -
    Complex.I * fderiv ℝ F x (rmul (toL (single i j (atEmb τ Complex.I))) x))

def detD (τ : K →+* ℂ) (F : Lie K n → ℂ) (x : Lie K n) : ℂ :=
  ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr (fun j G => pd τ (p j) j G) F x

def detAll (F : Lie K n → ℂ) : Lie K n → ℂ := (Finset.univ : Finset (K →+* ℂ)).toList.foldr detD F

def IsTest (Φ : Lie K n → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ invSet K n

def four (e : ℝ) (Φ : Lie K n → ℂ) (y : Lie K n) : ℂ :=
  ∫ x, Φ x * Complex.exp (Complex.I * ((e * ∑ w, ((Matrix.of x * Matrix.of y).trace w).re : ℝ) : ℂ))

end Defs

def Weyl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ) (U : Set (Lie K n)), IsOpen U →
    ∀ F : Lie K n → ℂ, ContDiffOn ℝ ∞ F U → ∀ x ∈ U, detAt τ x * detD τ F x =
      ∑ p : Equiv.Perm (Fin n), (((Equiv.Perm.sign p : ℤˣ) : ℤ) : ℂ) * (List.finRange n).foldr
        (fun j G y => rd τ (p j) j G y + (if p j = j then ((n - 1 - j.val : ℕ) : ℂ) else 0) * G y) F x

def Ptw : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ) (φ : Sm K n) (m : Multiset ℂ),
    (∀ u, cap τ u φ = (m.map (u + ·)).prod • φ) → ∀ (g : GA K n) (u : ℂ) (e : (K →+* ℂ) → ℕ), ∀ x ∈ invSet K n,
      detD τ (fun y => chart φ.1 g y * wt u e y) x =
        (m.map (u - e τ + ((n : ℂ) - 1) / 2 + ·)).prod * (chart φ.1 g x * wt u e x * (detAt τ x)⁻¹)

def Parts : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ) (Φ : Lie K n → ℂ), IsTest Φ →
    IsTest (detD τ Φ) ∧ ∀ F : Lie K n → ℂ, ContDiffOn ℝ ∞ F (invSet K n) →
      ∫ x, detD τ Φ x * F x = (-1) ^ n * ∫ x, Φ x * detD τ F x

def ShiftL : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), ∃ k : ℂ, k ≠ 0 ∧
    ∀ (φ : Sm K n) (m : (K →+* ℂ) → Multiset ℂ), (∀ τ u, cap τ u φ = ((m τ).map (u + ·)).prod • φ) →
    ∀ Φ : Lie K n → ℂ, IsTest Φ → IsTest (detAll Φ) ∧ ∀ (g : GA K n) (s : ℂ),
      ∫ x, detAll Φ x * chart φ.1 g x * ((nrm x : ℝ) : ℂ) ^ (s + 1 + ((n : ℂ) - 1) / 2 - n) =
        k * (linPoly (∑ τ, m τ)).eval s * ∫ x, Φ x * chart φ.1 g x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2 - n)

def FourD : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (e : ℝ), e ≠ 0 → ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ Φ : Lie K n → ℂ, IsTest Φ → ∀ y, four e (detAll Φ) y = κ * (nrm y : ℝ) * four e Φ y

def TestEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (f : Lie K n → ℂ), ContinuousOn f (invSet K n) →
    (∃ x ∈ invSet K n, f x ≠ 0) → ∃ Φ : Lie K n → ℂ, IsTest Φ ∧
      (Differentiable ℂ fun s : ℂ => ∫ x, Φ x * f x * ((nrm x : ℝ) : ℂ) ^ s) ∧
      ∃ s : ℂ, ∫ x, Φ x * f x * ((nrm x : ℝ) : ℂ) ^ s ≠ 0

def HaarL : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) [MeasurableSpace (GL (Fin n) (Cinf K))]
    [BorelSpace (GL (Fin n) (Cinf K))], ∃ m : Measure (GL (Fin n) (Cinf K)), m.IsHaarMeasure ∧
      Measure.map (fun g : GL (Fin n) (Cinf K) => toL g.val) m =
        ((volume : Measure (Lie K n)).restrict (invSet K n)).withDensity fun x => ENNReal.ofReal ((nrm x)⁻¹ ^ n)

def PtwOf : Prop := Weyl → Ptw
def ShiftOf : Prop := Ptw → Parts → ShiftL

end UpperTheory.V.Z.Inf
