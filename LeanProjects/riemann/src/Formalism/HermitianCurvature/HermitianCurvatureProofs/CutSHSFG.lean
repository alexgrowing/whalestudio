import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2

open MeasureTheory
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def pt {k ρ m : ℕ} (e : ρ + 1 = m) (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ) : B.Mat k m :=
  (rn1 e xx.1)⁻¹ * mc e t γ * rn1 e xx.2

def GfStep : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (z z' : Fin (2 * ρ + k + 1) → ℂ), inWb k ρ z → inWb k ρ z' →
    ∀ (t : ℂ), t ≠ 0 → ∀ (γ : B.Mat k ρ)
    (xx : U.RC k 1 ρ × U.RC k 1 ρ),
    Gf k m (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z)))
        (D.castV e (D.castV (Nat.add_comm 1 ρ) (liftVec k 1 ρ z'))) (pt e t γ xx) =
      ‖t‖ ^ 2 * Gf k ρ z z' γ

def RadProper : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (δ R : ℝ), 0 < δ →
    ∃ (Kx : Set (U.RC k 1 ρ × U.RC k 1 ρ)) (C : Set (B.Mat k ρ)), IsCompact Kx ∧ IsCompact C ∧
      ∀ (t : ℂ) (γ : B.Mat k ρ) (xx : U.RC k 1 ρ × U.RC k 1 ρ), δ ≤ ‖t‖ → B.gN (pt e t γ xx) ≤ R →
        xx ∈ Kx ∧ γ ∈ C

def ParamSmooth : Prop :=
  ∀ (Pm X W : Type) [NormedAddCommGroup Pm] [NormedSpace ℝ Pm] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (h : Pm → X → W) (s : Set Pm) (K : Set X),
    IsOpen s → IsCompact K → (∀ p ∈ s, ∀ x, x ∉ K → h p x = 0) →
    ContDiffOn ℝ ∞ (fun q : Pm × X => h q.1 q.2) (s ×ˢ Set.univ) →
    ContDiffOn ℝ ∞ (fun p => ∫ x, h p x ∂μ) s

def PtSmooth : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m),
    ContDiffOn ℝ ∞ (fun q : (ℂ × B.Mat k ρ) × (U.RC k 1 ρ × U.RC k 1 ρ) => pt e q.1.1 q.1.2 q.2)
      ({p : ℂ × B.Mat k ρ | p.1 ≠ 0} ×ˢ Set.univ) ∧
    ∀ z : Fin (2 * m + k + 1) → ℂ, ContDiff ℝ ∞ (fun x : U.RC k 1 ρ => psi k m z cStd (rn1 e x))

def PtGV : Prop :=
  ∀ (k ρ m : ℕ) (e : ρ + 1 = m) (t : ℂ), t ≠ 0 → ∀ γ ∈ B.GV k ρ, ∀ xx : U.RC k 1 ρ × U.RC k 1 ρ,
    pt e t γ xx ∈ B.GV k m

def CkExt : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E),
    B.CkOn (⊤ : ℕ∞) (B.GV k r) F → HasCompactSupport F →
    ∃ Ft : B.Mat k r → E, ContDiff ℝ ∞ Ft ∧ HasCompactSupport Ft ∧ ∀ g ∈ B.GV k r, Ft g = F g

end Formalism.FourierDecayAlt.P.CutSH.SFG
