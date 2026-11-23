import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpMRad

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdUv

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdUv (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f - pbOp ⟨r - 1, by omega⟩ f else cbiOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdUv r Y (m + 1) b f - pbOp ⟨r - (m + 2), by omega⟩ (tdUv r Y (m + 1) b f) -
          cbOp ⟨r - (m + 1), by omega⟩ (cbiOp ⟨r - (m + 2), by omega⟩ (tdUv r Y m b f))
      else fun _ => 0

end tdUv

def JDRvCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdUv r Y r b f c = Q.cmp (Q.vABs r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
