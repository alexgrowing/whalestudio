import Mathlib

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.MomentRationality.Cz.Pk

abbrev G (ι : Type) (N : ℕ) : Type := ι → SpecialLinearGroup (Fin N) ℂ

variable {ι : Type} {N : ℕ}

abbrev mt (x : G ι N) (w : ι) : Matrix (Fin N) (Fin N) ℂ :=
  ((x w : SpecialLinearGroup (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)

def dg (s : Fin N → ℝ) (hs : ∑ i, s i = 0) : G ι N := fun _ =>
  ⟨diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ), by
    rw [det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, hs, Real.exp_zero, Complex.ofReal_one]⟩

def Cone (T : ℝ) (s : Fin N → ℝ) : Prop := ∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T

def W (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if (j : ℕ) = i + 1 then |s i - s j| else 0

def Phi (s : Fin N → ℝ) : ℝ := ∑ i : Fin N, ∑ j : Fin N, if i < j then s i - s j else 0

def PB (M : ℝ) : Set (G ι N) := {p | ∀ w, (mt p w).BlockTriangular id ∧ ∀ i j, ‖mt p w i j‖ ≤ M}

def KS : Set (G ι N) := {k | ∀ w, mt k w ∈ unitaryGroup (Fin N) ℂ}

def OmG [Fintype ι] (M : ℝ) : Set (G ι N) :=
  {p | (∀ w, (mt p w).BlockTriangular id) ∧ (∀ w i j, ‖mt p w i j‖ ≤ M) ∧ (∀ w i, M⁻¹ ≤ ‖mt p w i i‖) ∧
    ∀ i, ∏ w, ‖mt p w i i‖ = 1}

def Sg (P : Set (G ι N)) (T : ℝ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), (∀ i j : Fin N, (j : ℕ) = i + 1 → s j ≤ s i + T) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Xb (P : Set (G ι N)) (T : ℝ) (m : Fin N → ℤ) : Set (G ι N) :=
  {x | ∃ p ∈ P, ∃ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s ∧ (∀ i, (m i : ℝ) ≤ s i ∧ s i ≤ m i + 1) ∧
    ∃ k ∈ KS, x = p * dg s hs * k}

def Zb (R : ℝ) : Set (G ι N) := {z | ∀ w i j, ‖mt z w i j‖ ≤ R}

open Classical in

def nu (w0 : ι) : SpecialLinearGroup (Fin N) GaussianInt →* G ι N :=
  (MonoidHom.mulSingle (fun _ : ι => SpecialLinearGroup (Fin N) ℂ) w0).comp
    (SpecialLinearGroup.map GaussianInt.toComplex)

end PositivityTheory.KB.MomentRationality.Cz.Pk

end
