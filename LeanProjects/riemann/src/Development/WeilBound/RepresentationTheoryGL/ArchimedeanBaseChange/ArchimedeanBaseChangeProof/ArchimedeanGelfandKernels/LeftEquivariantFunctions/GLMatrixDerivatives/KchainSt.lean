import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.FrameDer

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate ComplexOrder

namespace PositivityTheory.RgBcC.LfSt.Kchain

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def InvSmooth : Prop := ∀ n : ℕ, IsOpen (GLs n) ∧ ContDiffOn ℝ ∞ (fun y : Mat n => y⁻¹) (GLs n) ∧
  ContDiffOn ℝ ∞ (fun y : Mat n => yᴴ⁻¹) (GLs n) ∧ ContDiff ℝ ∞ (fun y : Mat n => y.det) ∧
  ContDiff ℝ ∞ (fun y : Mat n => yᴴ)

def ConeGL : Prop := ∀ (n : ℕ) (σ : (Fin n × Fin n → ℝ) → Mat n), (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) →
  ∀ v ∈ cone n, σ v ∈ GLs n ∧ (hOf v).det ≠ 0

def KcSmooth : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (σ : (Fin n × Fin n → ℝ) → Mat n) (c : ℝ)
    (Fr k : Mat n → (V →L[ℂ] V)) (Γ T : V →L[ℂ] V) (d : Mat n), d ∈ GLs n → ContDiffOn ℝ ∞ σ (cone n) →
    (∀ v ∈ cone n, σ v * (σ v)ᴴ = hOf v) → ContDiffOn ℝ ∞ Fr (GLs n) → ContDiffOn ℝ ∞ k (GLs n) →
    ContDiffOn ℝ ∞ (Kc σ c Fr k Γ T d) (cone n ×ˢ cone n)

def FrMul : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ x ∈ GLs n, ∀ Y : Mat n,
    fderiv ℝ Fr x (x * Y) = Fr x * fderiv ℝ Fr 1 Y

def FrComm : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T → ∀ X H : Mat n, X.IsHermitian → H.IsHermitian →
    fderiv ℝ Fr 1 X * ε H = ε H * fderiv ℝ Fr 1 X - ε (X * H + H * X) ∧ Γ * fderiv ℝ Fr 1 X = fderiv ℝ Fr 1 X * Γ

def DerOne : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) → ∀ (d y : Mat n), d ∈ GLs n → y ∈ GLs n →
    ∀ x ∈ GLs n, ∀ X : Mat n,
      fderiv ℝ (fun x' => Kf Fr k Γ T d x' y) x (x * X) =
        Fr x * (fderiv ℝ Fr 1 X * k (x⁻¹ * d * yᴴ⁻¹) + Ld X k (x⁻¹ * d * yᴴ⁻¹)) * Γ * T * Fr y⁻¹

def wt (c : ℝ) (y : Mat n) : ℂ := (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹

def DerTwo : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℤ) E Fr ε ι S Γ T, CxData lam E Fr ε ι S Γ T →
    ∀ (k : Mat n → (E.V →L[ℂ] E.V)), ContDiffOn ℝ ∞ k (GLs n) → ∀ (c : ℝ) (d x : Mat n), d ∈ GLs n → x ∈ GLs n →
    ∀ y ∈ GLs n, ∀ X : Mat n, X.IsHermitian →
      fderiv ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y (y * X) =
        wt c y • (Fr x * (((-(2 * n : ℂ)) * X.trace) • k (x⁻¹ * d * yᴴ⁻¹) * Γ * T -
          Rd X k (x⁻¹ * d * yᴴ⁻¹) * Γ * T - k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * fderiv ℝ Fr 1 X) * Fr y⁻¹)

def DualSum : Prop :=
  ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (α β : Mat n →ₗ[ℝ] (V →L[ℂ] V))
    (A A' : Fin n × Fin n → Mat n), (∀ i, (A i).IsHermitian) → (∀ i, (A' i).IsHermitian) →
    (∀ i j, (A i * A' j).trace = if i = j then 1 else 0) →
    ∑ i, α (A i) * β (A' i) = ∑ p, α (hb p) * β (hb p)

end PositivityTheory.RgBcC.LfSt.Kchain
