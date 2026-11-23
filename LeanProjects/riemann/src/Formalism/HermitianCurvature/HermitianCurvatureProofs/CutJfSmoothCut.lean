import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFFName
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvariantOperatorUnderJacquet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JfS

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section ellreg

variable {d : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

def pd : List (Fin d) → ((Fin d → ℝ) → F) → (Fin d → ℝ) → F
  | [], u => u
  | i :: w, u => fun x => fderiv ℝ (pd w u) x (Pi.single i 1)

def applyOp {N M : ℕ} (m : ℕ) (a : (k : Fin (m + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (u : (Fin d → ℝ) → (Fin N → ℝ)) (x : Fin d → ℝ) : Fin M → ℝ :=
  ∑ k : Fin (m + 1), ∑ w : Fin k → Fin d, a k w x *ᵥ pd (List.ofFn w) u x

def transposeOp {N M : ℕ} (m : ℕ) (a : (k : Fin (m + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (φ : (Fin d → ℝ) → (Fin M → ℝ)) (x : Fin d → ℝ) : Fin N → ℝ :=
  ∑ k : Fin (m + 1), ∑ w : Fin k → Fin d, ((-1 : ℝ) ^ (k : ℕ)) • pd (List.ofFn w) (fun y => (a k w y)ᵀ *ᵥ φ y) x

def symb {N M : ℕ} (m : ℕ) (a : (k : Fin (m + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (x ξ : Fin d → ℝ) : Matrix (Fin M) (Fin N) ℝ :=
  ∑ w : Fin m → Fin d, (∏ i, ξ (w i)) • a (Fin.last m) w x

def IsWeakSol {N M : ℕ} (U : Set (Fin d → ℝ)) (m : ℕ)
    (a : (k : Fin (m + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → Matrix (Fin M) (Fin N) ℝ)
    (u : (Fin d → ℝ) → (Fin N → ℝ)) (f : (Fin d → ℝ) → (Fin M → ℝ)) : Prop :=
  ∀ φ : (Fin d → ℝ) → (Fin M → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    ∫ x, transposeOp m a φ x ⬝ᵥ u x = ∫ x, φ x ⬝ᵥ f x

end ellreg

def EllReg : Prop :=
  ∀ (d N : ℕ) (ι : Type) [Fintype ι] (M m : ι → ℕ)
    (a : ∀ j, (k : Fin (m j + 1)) → (Fin k → Fin d) → (Fin d → ℝ) → Matrix (Fin (M j)) (Fin N) ℝ)
    (f : ∀ j, (Fin d → ℝ) → (Fin (M j) → ℝ)) (U : Set (Fin d → ℝ)) (u : (Fin d → ℝ) → (Fin N → ℝ)),
    IsOpen U → (∀ j k w, ContDiffOn ℝ ∞ (a j k w) U) → (∀ j, ContDiffOn ℝ ∞ (f j) U) → ContinuousOn u U →
    (∀ j, IsWeakSol U (m j) (a j) u (f j)) →
    (∀ x ∈ U, ∀ ξ : Fin d → ℝ, ξ ≠ 0 → ∀ v : Fin N → ℝ, (∀ j, symb (m j) (a j) x ξ *ᵥ v = 0) → v = 0) →
    ContDiffOn ℝ ∞ u U

def lieOf {k r : ℕ} (Sx : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Sx}

def InLevi (k r : ℕ) (ξ : B.Mat k r) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), ξ i j ≠ 0 → i = j ∨ (r ≤ i.val ∧ i.val ≤ r + k ∧ r ≤ j.val ∧ j.val ≤ r + k)

def OmQ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (B.Mat k r) :=
  {g | 0 < Gf k r z z' g ∧ ∀ a : Fin r, Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0}

def SymbolLevi : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      InLevi k r ξ

def SymbolW : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ → InLevi k r ξ →
      (∀ X ∈ lieOf (UWset k r z), (Matrix.trace (ξ * X)).re = 0) → ξ = 0

def SymbolNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ g ∈ B.GV k r, g ∈ OmQ k r z z' → ∀ ξ : B.Mat k r, B.inLie k r ξ → IsNilpotent ξ →
      (∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ξ * X)).re = 0) →
      (∀ X ∈ lieOf (Sset k r z'), (Matrix.trace (ξ * (g * X * g⁻¹))).re = 0) →
      ξ = 0

theorem lieOf_mono {k r : ℕ} {A B' : Set (B.Mat k r)} (h : A ⊆ B') : lieOf A ⊆ lieOf B' :=
  fun _ hX t => h (hX t)

theorem UWset_sub_Sset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : UWset k r z ⊆ Sset k r z :=
  fun h hh => ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

def convR {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (μ : MeasureTheory.Measure (Mt k r))
    (J : B.Mat k r → W) (φ : B.Mat k r → ℂ) (g : B.Mat k r) : W :=
  ∫ h, φ (Matrix.of h) • J (g * Matrix.of h) ∂μ

def DistEigen : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : NumberField.InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    JCT.IsBuiltPlace Cc S T f χ ν' m₀ top A₀ →
    ∀ (v : Fin S.f) (Y : ℝ) (φ : B.Mat S.G.k S.G.r → ℂ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∀ g ∈ B.GV S.G.k S.G.r, (∀ h ∈ tsupport φ, h ∈ B.GV S.G.k S.G.r → g * h ∈ OmP S T v) →
        Q.CV S.G.k S.G.r (Y : ℂ) (convR (T v).base.μG (B.JF (T v).base (f v)) φ) g =
          ((S.P v Y : ℝ) : ℂ) • convR (T v).base.μG (B.JF (T v).base (f v)) φ g

def Red : Prop := EllReg → SymbolNil → DistEigen → JF.JWords → JfSmoothBuilt

end

end Formalism.FourierDecayAlt.P.CutMP.JfS
