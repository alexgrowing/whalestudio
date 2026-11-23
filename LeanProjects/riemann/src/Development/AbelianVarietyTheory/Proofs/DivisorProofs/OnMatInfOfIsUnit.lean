import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

abbrev compGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w)

theorem compGL_apply (w : InfinitePlace E) (g : GL (Fin n) (Cinf E)) (i j : Fin n) :
    ((compGL w g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) i j = (g : Matrix (Fin n) (Fin n) (Cinf E)) i j w := rfl

abbrev matInf (g : GL (Fin n) (Cinf E)) : Fin n → Fin n → Cinf E :=
  fun i j => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j

def IsWhitInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), ∀ g,
    W (u * g) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * W g

def IsModGrowthInf (W : GL (Fin n) (Cinf E) → ℂ) : Prop :=
  Continuous W ∧ ∃ (C : ℝ) (N : ℕ), ∀ g, ‖W g‖ ≤ C * htInf g ^ N

def IsRapidFInf {X Z : Type} [MeasurableSpace X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin n) (Cinf E)) (η : X → Z →L[ℝ] ℝ) : Prop :=
  Measurable k ∧ (∀ i j, Measurable fun x => (γ x : Matrix (Fin n) (Fin n) (Cinf E)) i j) ∧
    (∀ z, Measurable fun x => η x z) ∧
    ∀ N : ℕ, Integrable (fun x => ‖k x‖ * (htInf (γ x) * (1 + ‖η x‖)) ^ N) ν

def IsKerOpInf {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ) : Prop :=
  ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin n) (Cinf E))
    (η : X → Z →L[ℝ] ℝ), IsRapidFInf ν k γ η ∧
      ∀ W, IsModGrowthInf W → ∀ z g, T W z g = ∫ x, k x * (𝐞 (η x z) : ℂ) * W (g * γ x) ∂ν

variable (E) in

def levSetInf (n r : ℕ) : Set (GL (Fin n) (Cinf E)) := {g | ∀ w, compGL w g ∈ levSet n r}

def rowCutInf (ρ : Fin n) (x : Matrix (Fin n) (Fin n) (Cinf E)) : Fin n → Cinf E := fun j => if j ≤ ρ then x ρ j else 0

def secMatInf (ρ : Fin n) (j : InfinitePlace E → Fin n) (v : Fin n → Cinf E) : Fin n → Fin n → Cinf E :=
  fun i l w => secMat ρ (j w) (fun l => v l w) i l

open Classical in

def onMatInf (W : GL (Fin n) (Cinf E) → ℂ) (x : Matrix (Fin n) (Fin n) (Cinf E)) : ℂ :=
  if h : IsUnit x then W h.unit else 0

def smoothMatInf (α : (Fin n → Fin n → Cinf E) → ℂ) (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) : ℂ :=
  ∫ a : Fin n → Fin n → Cinf E, α a * onMatInf W ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of a)

open Classical in

def toGLInf (x : Matrix (Fin n) (Fin n) (Cinf E)) : GL (Fin n) (Cinf E) := if h : IsUnit x then h.unit else 1

theorem val_toGLInf {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    (toGLInf x : Matrix (Fin n) (Fin n) (Cinf E)) = x := by
  simp [toGLInf, h]

theorem onMatInf_val (W : GL (Fin n) (Cinf E) → ℂ) (g : GL (Fin n) (Cinf E)) :
    onMatInf W (g : Matrix (Fin n) (Fin n) (Cinf E)) = W g := by
  simp [onMatInf]

theorem onMatInf_of_isUnit (W : GL (Fin n) (Cinf E) → ℂ) {x : Matrix (Fin n) (Fin n) (Cinf E)} (h : IsUnit x) :
    onMatInf W x = W (toGLInf x) := by
  simp [onMatInf, toGLInf, h]

theorem mem_levSetInf {r : ℕ} {g : GL (Fin n) (Cinf E)} : g ∈ levSetInf E n r ↔
    ∀ i : Fin n, r ≤ (i : ℕ) → (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
      (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1 := by
  constructor
  · intro h i hi
    refine ⟨fun j hj => funext fun w => ?_, funext fun w => ?_⟩
    · exact (h w i hi).1 j hj
    · exact (h w i hi).2
  · intro h w i hi
    refine ⟨fun j hj => ?_, ?_⟩
    · rw [compGL_apply, (h i hi).1 j hj]; rfl
    · rw [compGL_apply, (h i hi).2]; rfl

theorem isKerOpInf_dirac (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] (h : GL (Fin n) (Cinf E)) :
    IsKerOpInf (fun W (_ : Z) g => W (g * h)) := by
  refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => h, fun _ => 0,
    ⟨measurable_const, fun _ _ => measurable_const, fun _ => measurable_const, fun _ => integrable_const _⟩,
    fun W _ z g => ?_⟩
  simp

def LevRepInf (E : Type) [Field E] [NumberField E] (n r : ℕ) (lam : (GL (Fin n) (Cinf E) → ℂ) → ℂ) : Prop :=
  ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] (B : Y × (Fin n → Fin n → Cinf E) → ℂ),
    ContDiffOn ℝ ∞ B {p | IsUnit (Matrix.of p.2)} → (∀ y, IsWhitInf fun g => B (y, matInf g)) →
    (∃ (D : Set Y) (C : Set (GL (Fin n) (Cinf E))), IsCompact D ∧ IsCompact C ∧ ∀ y, ∀ g ∈ levSetInf E n r,
      B (y, matInf g) ≠ 0 → y ∈ D ∧ ∃ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u⁻¹ * g ∈ C) →
    ∃ T : (GL (Fin n) (Cinf E) → ℂ) → Y → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T ∧
      ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ y, ∀ g ∈ levSetInf E n r, T W y g = B (y, matInf g) * lam W

example (r : ℕ) : (1 : GL (Fin n) (Cinf E)) ∈ levSetInf E n r ∧
    IsKerOpInf (fun W (_ : ℝ) g => W (g * (1 : GL (Fin n) (Cinf E)))) := by
  refine ⟨mem_levSetInf.2 fun i _ => ⟨fun j hj => ?_, by simp⟩, isKerOpInf_dirac ℝ 1⟩
  simp [Matrix.one_apply, hj.ne']

end GlobalTheory.JSW.MirCinf
