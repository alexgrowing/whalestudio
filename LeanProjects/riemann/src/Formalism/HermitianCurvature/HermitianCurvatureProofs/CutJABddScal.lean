import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

def phiR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g ⟨r, by omega⟩ / Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1))

def phiD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ℂ :=
  Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)) / (starRingEnd ℂ) (Formalism.QuantumDeterminants.Dmin k r z z' g (Fin.last (r + 1)))

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def ScalOK (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ) : Prop :=
  B.CkOn ⊤ (B.GPos D) φ ∧
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C : ℝ, ∀ u w : List (B.Mat k r),
    (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV k r, ε ≤ Formalism.QuantumDeterminants.Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m)

end

def JAScalBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ), K * ((r : ℝ) + 1) ≤ Bg →
    ScalOK D Bg (phiR k r D.z D.z') ∧ ScalOK D Bg (phiD k r D.z D.z')

def JAScalConj : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (Bg : ℝ) (φ : B.Mat k r → ℂ),
    ScalOK D Bg φ → ScalOK D Bg (fun g => (starRingEnd ℂ) (φ g))

end

end Formalism.FourierDecayAlt.P.CutMP.JA
