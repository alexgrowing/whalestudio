import Mathlib
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombinationStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFpmDecay
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConjEntrySmulCapelliEigenSum
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory.EigenSumPoly

section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def IsEigenSum (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ),
    (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧
    (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧
    (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g =
      ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧
    ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g

def entryVar (g : B.Mat k r) :
    (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) → ℂ :=
  Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))

end

end GlobalTheory.EigenSumPoly
