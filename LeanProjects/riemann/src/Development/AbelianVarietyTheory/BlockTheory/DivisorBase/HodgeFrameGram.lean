import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram

section Defs

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {ι : Type} [Fintype ι] {n : ℕ}

structure IsFlagFamily (Y : Set E) (U : Set (ι → ℂ)) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) : Prop where

  isOpen : IsOpen Y

  hol_proj : ContDiffOn ℂ ∞ π Y

  mapsTo : Set.MapsTo π Y U

  hol_frame : ∀ a b, ContDiffOn ℂ ∞ (fun y => A y a b) Y

  isUnit : ∀ y ∈ Y, IsUnit (A y).det

def flagDeriv (A : E → Matrix (Fin n) (Fin n) ℂ) (y ξ : E) : Matrix (Fin n) (Fin n) ℂ :=
  (A y)⁻¹ * mdel A y ξ

def FixesFlag (A : E → Matrix (Fin n) (Fin n) ℂ) (y ξ : E) : Prop :=
  ∀ i l, i < l → flagDeriv A y ξ l i = 0

def IsFlagChartAt (π : E → ι → ℂ) (A : E → Matrix (Fin n) (Fin n) ℂ) (y : E) : Prop :=
  (∀ ξ, fderiv ℂ π y ξ = 0 → FixesFlag A y ξ → ξ = 0) ∧
    ∀ (v : ι → ℂ) (T : Matrix (Fin n) (Fin n) ℂ),
      ∃ ξ, fderiv ℂ π y ξ = v ∧ ∀ i l, i < l → flagDeriv A y ξ l i = T l i

def adaptedGram (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (y : E) : Matrix (Fin n) (Fin n) ℂ :=
  (A y)ᵀ * H (π y) * (A y)ᴴᵀ

def lineGram (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (y : E) : Matrix Unit Unit ℂ :=
  gradedGram (adaptedGram H π A y) i

def weightNormSq (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (A : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y : E) : ℝ :=
  ∏ i, (lineGram H π A i y () ()).re ^ (-lam i)

def lineChern (f : E → ℝ) (y ξ η : E) : ℂ :=
  chernOne (fun x => (of fun _ _ => (f x : ℂ) : Matrix Unit Unit ℂ)) y ξ η

structure IsUnitaryFlagFrame (Y : Set E) (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (π : E → ι → ℂ) (A e : E → Matrix (Fin n) (Fin n) ℂ) : Prop where

  smooth : ∀ a b, ContDiffOn ℝ ∞ (fun y => e y a b) Y

  unitary : ∀ y ∈ Y, ∀ k l,
    form (H (π y)) (fun a => e y a k) (fun a => e y a l) = if k = l then 1 else 0

  mem : ∀ y ∈ Y, ∀ i,
    (fun a => e y a i) ∈ Submodule.span ℂ {v : Fin n → ℂ | ∃ j ≤ i, v = fun a => A y a j}

  perp : ∀ y ∈ Y, ∀ i j, j < i → form (H (π y)) (fun a => e y a i) (fun a => A y a j) = 0

def thetaOneZero (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (y ξ : E) : Matrix (Fin n) (Fin n) ℂ :=
  (e y)⁻¹ * (mdel e y ξ + conn H (π y) (fderiv ℂ π y ξ) * e y)

def thetaZeroOne (e : E → Matrix (Fin n) (Fin n) ℂ) (y η : E) : Matrix (Fin n) (Fin n) ℂ :=
  (e y)⁻¹ * mdbar e y η

def thetaSq (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (l i : Fin n) (y ξ η : E) : ℂ :=
  thetaOneZero H π e y ξ l i * conj (thetaOneZero H π e y η l i)

def curvDiag (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (y ξ η : E) : ℂ :=
  form (H (π y)) (curv H (π y) (fderiv ℂ π y ξ) (fderiv ℂ π y η) *ᵥ fun a => e y a i)
    fun a => e y a i

def vertForm (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y ξ η : E) : ℂ :=
  kappa * ∑ i, ∑ l ∈ Finset.Ioi i, ((lam i - lam l : ℝ) : ℂ) * thetaSq H π e l i y ξ η

def horizForm (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y ξ η : E) : ℂ :=
  -(kappa * ∑ i, (lam i : ℂ) * curvDiag H π e i y ξ η)

def pullForm (G : (ι → ℂ) → Matrix ι ι ℂ) (π : E → ι → ℂ) (y ξ η : E) : ℂ :=
  formOf (G (π y)) (fderiv ℂ π y ξ) (fderiv ℂ π y η)

def pairWeightNormSq {T : Type} [Fintype T] {p q : T → ℕ}
    (HW : ∀ τ, (ι → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Hω : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (π : E → ι → ℂ)
    (AW : ∀ τ, E → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, E → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (lam : ∀ τ, Fin (p τ + q τ) → ℝ) (y : E) :
    ℝ :=
  ∏ τ, weightNormSq (HW τ) π (AW τ) (fun i => lam τ (Fin.castAdd (q τ) i)) y *
    weightNormSq (Hω τ) π (Aω τ) (fun i => lam τ (Fin.natAdd (p τ) i)) y

structure IsHodgeFrame {p q : ℕ} (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) : Prop where

  isHermFrame : IsHermFrame U ψ

  flat : ∀ x ∈ U, ∀ v w, curv ψ x v w = 0

  neg_sub : ∀ x ∈ U, (-subGram (ψ x)).PosDef

  pos_quot : ∀ x ∈ U, (quotGram (ψ x)).PosDef

end Defs

def GradedLineCurvature : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (n : ℕ) (U : Set (ι → ℂ))
    (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (A e : E → Matrix (Fin n) (Fin n) ℂ),
    IsPosFrame U H → IsFlagFamily Y U π A → IsUnitaryFlagFrame Y H π A e →
    ∀ y ∈ Y,
      (∀ k l η, thetaZeroOne e y η k l = -conj (thetaOneZero H π e y η l k)) ∧
      (∀ k l η, k < l → thetaZeroOne e y η l k = 0) ∧
      (∀ i ξ η, curv (lineGram H π A i) y ξ η () () =
        curvDiag H π e i y ξ η - ∑ l ∈ Finset.Ioi i, thetaSq H π e l i y ξ η
          + ∑ l ∈ Finset.Iio i, thetaSq H π e i l y ξ η) ∧
      ∀ lam : Fin n → ℝ,
        (∀ ξ η, lineChern (weightNormSq H π A lam) y ξ η =
          vertForm H π e lam y ξ η + horizForm H π e lam y ξ η) ∧
        (Antitone lam → FormLe (fun _ _ => 0) (vertForm H π e lam y)) ∧
        (IsFlagChartAt π A y →
          ((∀ ξ, ξ ≠ 0 → fderiv ℂ π y ξ = 0 → 0 < diagVal (vertForm H π e lam y) ξ) ↔
            StrictAnti lam)) ∧
        ∀ (G : (ι → ℂ) → Matrix ι ι ℂ) (C : ℝ), TwoFormBound U H G (curv H) C →
          FormAbsLe (horizForm H π e lam y) (1 / (2 * Real.pi) * (∑ i, |lam i|) * C)
            (pullForm G π y)

def ChernLowerBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (T : Type) [Fintype T] (p q : T → ℕ)
    (U : Set (ι → ℂ)) (HW : ∀ τ, (ι → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Hω : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (Y : Set E) (π : E → ι → ℂ)
    (AW : ∀ τ, E → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, E → Matrix (Fin (q τ)) (Fin (q τ)) ℂ) (G : (ι → ℂ) → Matrix ι ι ℂ) (C : ℝ),
    (∀ τ, IsPosFrame U (HW τ)) → (∀ τ, IsPosFrame U (Hω τ)) →
    (∀ τ, IsFlagFamily Y U π (AW τ)) → (∀ τ, IsFlagFamily Y U π (Aω τ)) →
    (∀ τ, TwoFormBound U (HW τ) G (curv (HW τ)) C) →
    (∀ τ, TwoFormBound U (Hω τ) G (curv (Hω τ)) C) →
    ∀ lam : ∀ τ, Fin (p τ + q τ) → ℝ,
      (∀ τ, Antitone fun i => lam τ (Fin.castAdd (q τ) i)) →
      (∀ τ, Antitone fun i => lam τ (Fin.natAdd (p τ) i)) →
      ∀ y ∈ Y,
        FormLe (fun ξ η => ((-(C / (2 * Real.pi)) * ∑ τ, ∑ i, |lam τ i| : ℝ) : ℂ) *
            pullForm G π y ξ η)
          (lineChern (pairWeightNormSq HW Hω π AW Aω lam) y)

def HodgePositivity : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (T : Type) [Fintype T] (p q : T → ℕ)
    (U : Set (ι → ℂ)) (ψ : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ) ⊕ Fin (p τ)) (Fin (q τ) ⊕ Fin (p τ)) ℂ)
    (a b : T → ℝ) (Y : Set E) (π : E → ι → ℂ)
    (AW : ∀ τ, E → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, E → Matrix (Fin (q τ)) (Fin (q τ)) ℂ),
    (∀ τ, IsHodgeFrame U (ψ τ)) → (∀ τ, 0 < a τ) → (∀ τ, 0 < b τ) →
    (∀ τ, IsFlagFamily Y U π (AW τ)) → (∀ τ, IsFlagFamily Y U π (Aω τ)) →
    ∀ (lam : ∀ τ, Fin (p τ + q τ) → ℝ), ∀ y ∈ Y,
      ((∀ τ, Antitone (lam τ)) →
        FormLe (fun _ _ => 0)
          (lineChern (pairWeightNormSq (fun τ x => (a τ : ℂ) • quotGram (ψ τ x))
            (fun τ x => (b τ : ℂ) • -subGram (ψ τ x)) π AW Aω lam) y)) ∧
      ((∀ τ, StrictAnti (lam τ)) →
        (∀ v, (∀ τ, secondForm (ψ τ) (π y) v = 0) → v = 0) →
        (∀ ξ, fderiv ℂ π y ξ = 0 → (∀ τ, FixesFlag (AW τ) y ξ) → (∀ τ, FixesFlag (Aω τ) y ξ) →
          ξ = 0) →
        ∀ ξ, ξ ≠ 0 → 0 < diagVal
          (lineChern (pairWeightNormSq (fun τ x => (a τ : ℂ) • quotGram (ψ τ x))
            (fun τ x => (b τ : ℂ) • -subGram (ψ τ x)) π AW Aω lam) y) ξ)

def Statement : Prop := GradedLineCurvature ∧ ChernLowerBound ∧ HodgePositivity

section Examples

def cellFrame (y : (Fin 1 → ℂ) × ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; y.2, 1]

def cellUnitary (y : (Fin 1 → ℂ) × ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (((√(1 + ‖y.2‖ ^ 2))⁻¹ : ℝ) : ℂ) • !![1, -conj y.2; y.2, 1]

def discFrame (x : Fin 1 → ℂ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks 1 0 (of fun _ _ => x 0) 1

def discGram (x : Fin 1 → ℂ) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  (discFrame x)ᵀ * fromBlocks (-1) 0 0 1 * (discFrame x)ᴴᵀ

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
