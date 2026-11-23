import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRGrpPPComm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section tdU

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

def tdU (r : ℕ) (Y : ℂ) : ℕ → Fin 2 → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0, b => if b = 0 then id else fun _ => 0
  | 1, b => if h : 1 ≤ r then (if b = 0 then fun f => Y • f + pOp ⟨r - 1, by omega⟩ f else ciOp ⟨r - 1, by omega⟩)
      else fun _ => 0
  | m + 2, b => if h : m + 2 ≤ r then
        fun f => Y • tdU r Y (m + 1) b f + pOp ⟨r - (m + 2), by omega⟩ (tdU r Y (m + 1) b f) -
          cOp ⟨r - (m + 1), by omega⟩ (ciOp ⟨r - (m + 2), by omega⟩ (tdU r Y m b f))
      else fun _ => 0

end tdU

def JDRCont : Prop :=
  ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (r : ℕ) (Y : ℂ) (O : Set (Fin r → ℂ)), IsOpen O → O ⊆ OmX r →
    ∀ f : (Fin r → ℂ) → X, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f O → ∀ c ∈ O, ∀ b : Fin 2,
      tdU r Y r b f c = Q.cmp (Q.vAB r Y r) b f c

end

end Formalism.FourierDecayAlt.P.CutMP
