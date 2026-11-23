import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section Concrete

variable (l : ℕ) [Fact l.Prime]

def muP : Set ℂ_[l] := {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1}

def Rmu : Subring ℂ_[l] := Subring.closure (muP l)

def Kmu : Subfield ℂ_[l] := Subfield.closure (muP l)

def Tch : Set ℂ_[l] := insert 0 (muP l)

theorem kur_complete : CompleteSpace (MaximalUnramifiedExtension l) :=
  (Subfield.isClosed_topologicalClosure (Kmu l)).completeSpace_coe

end Concrete

structure FrobField (K : Type) [NormedField K] (l : ℕ) (σ : K →+* K) : Prop where
  prime : l.Prime
  norm_l : ‖(l : K)‖ < 1
  isom : ∀ x : K, ‖σ x‖ = ‖x‖
  frob : ∀ x : K, ‖x‖ ≤ 1 → ‖σ x - x ^ l‖ ≤ ‖(l : K)‖
  discrete : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : K)‖

def ResClosed (K : Type) [NormedField K] (l : ℕ) : Prop :=
  ∀ P : Polynomial K, P.Monic → 0 < P.natDegree → (∀ i, ‖P.coeff i‖ ≤ 1) →
    ∃ x : K, ‖x‖ ≤ 1 ∧ ‖P.eval x‖ ≤ ‖(l : K)‖

end ReciprocityTheory.ChartRestriction.L1
