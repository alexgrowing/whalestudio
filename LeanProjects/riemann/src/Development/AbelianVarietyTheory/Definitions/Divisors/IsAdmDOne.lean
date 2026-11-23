import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied

noncomputable section

namespace GlobalTheory.AdmBr

open Formalism.Per

variable {l : ℕ} [Fact l.Prime]

def IsAdmD (q : ℚ_[l] →+* BdR l) (S : Set (BdR l)) {d : ℕ} (G : Subgroup (Gq l)) (r : G → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
    ∀ σ : G, (r σ).map q * P.map (σD σ.1) = P

end GlobalTheory.AdmBr
