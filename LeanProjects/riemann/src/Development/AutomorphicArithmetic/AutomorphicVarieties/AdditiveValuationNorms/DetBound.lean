import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.DetFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.PadicUnitsDistanceLeMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.NormVal

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.detBound :
    ∀ (l : ℕ) [Fact l.Prime] (u : ℤ_[l]) (c : ℕ), IsLevel l u c → ∀ (j R : ℕ) (S : Matrix (Fin R) (Fin R) ℤ_[l]),
      ∃ s : Fin R → ℤ_[l], ∀ e : ℕ, vl l ((u ^ l ^ j) ^ e • S - 1).det ≤ ∑ i, (((j + c : ℕ) : ℕ∞) + vl l (s i - e)) := by
  intro l _ u c hc j R S
  let φ : ℤ_[l] →+* PadicAlgCl l := (algebraMap ℚ_[l] (PadicAlgCl l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, ‖φ x‖ = ‖x‖ := by
    intro x
    show ‖algebraMap ℚ_[l] (PadicAlgCl l) (x : ℚ_[l])‖ = ‖x‖
    rw [← PadicInt.padic_norm_e_of_padicInt]
    exact PadicAlgCl.norm_extends l (x : ℚ_[l])
  obtain ⟨z, hz⟩ := detFactor (PadicAlgCl l) R (S.map φ)
  choose s hs using fun i => ball l u c hc j (z i)
  refine ⟨s, fun e => ?_⟩
  apply normVal l R (j + c) _ (fun i => s i - e)
  set a : ℤ_[l] := (u ^ l ^ j) ^ e with ha
  have hdet : φ (a • S - 1).det = ∏ i, (φ a * z i - 1) := by
    rw [RingHom.map_det, ← hz (φ a)]
    congr 1
    ext p q
    simp [Matrix.sub_apply, Matrix.one_apply, RingHom.mapMatrix_apply]
  rw [← hφ, hdet, norm_prod]
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i _
    exact hs i e
