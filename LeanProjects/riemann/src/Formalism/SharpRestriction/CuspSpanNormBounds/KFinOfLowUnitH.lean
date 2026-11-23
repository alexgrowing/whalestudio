import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselBoundFamilyOfDoubleCoset

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace Formalism.MainNotions.KFiniteLowUnitary

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.TheoremBConstants Formalism.MainNotions.DiscreteSeriesInnerProducts Formalism.MainNotions.CayleySignature Formalism.MainNotions.S.UnitaryLevelOperators

section Low

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem conj_mem_Kset' {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r} (hP : IsCayleyU k r ε P) {g : Mat k r}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (hgu : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) :
    P * g * P⁻¹ ∈ Formalism.REAL.Kset ε := by
  have hPu := hP.2
  have hPs : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hPu
  have hPs' : P * star P = 1 := Matrix.mem_unitaryGroup_iff.1 hPu
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv hPs
  have hgs : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hgu
  have hcay : star P * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := by
    rw [Matrix.star_eq_conjTranspose]; exact hP.1.2
  have hg' : star g * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := by
    rw [Matrix.star_eq_conjTranspose]; exact hg

  have hcomm : Formalism.QuantumDeterminants.Hpk k r * g = g * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * g = (g * star g) * Formalism.QuantumDeterminants.Hpk k r * g := by rw [hgs, Matrix.one_mul]
      _ = g * (star g * Formalism.QuantumDeterminants.Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = g * Formalism.QuantumDeterminants.Hpk k r := by rw [hg']

  have hJ : Formalism.REAL.Jm ε = P * Formalism.QuantumDeterminants.Hpk k r * star P := by
    rw [← hcay]
    calc Formalism.REAL.Jm ε = (P * star P) * Formalism.REAL.Jm ε * (P * star P) := by
          rw [hPs', Matrix.one_mul, Matrix.mul_one]
      _ = P * (star P * Formalism.REAL.Jm ε * P) * star P := by simp only [Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPu hgu) (Matrix.mem_unitaryGroup_iff.2 (by rw [star_star]; exact hPs))
  · rw [hinv, hJ]
    calc P * g * star P * (P * Formalism.QuantumDeterminants.Hpk k r * star P)
        = P * g * (star P * P) * Formalism.QuantumDeterminants.Hpk k r * star P := by simp only [Matrix.mul_assoc]
      _ = P * (g * Formalism.QuantumDeterminants.Hpk k r) * star P := by rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * (Formalism.QuantumDeterminants.Hpk k r * g) * star P := by rw [hcomm]
      _ = P * Formalism.QuantumDeterminants.Hpk k r * (star P * P) * g * star P := by
          rw [hPs, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = P * Formalism.QuantumDeterminants.Hpk k r * star P * (P * g * star P) := by simp only [Matrix.mul_assoc]

theorem kFin_of_lowUnitH' {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mat k r → (H →L[ℂ] H)} {w : H} (hw : IsLowUnitH k r ε lam σ w) : IsKFinHpk (k := k) (r := r) σ w := by
  obtain ⟨P, hP, -, hmem⟩ := hw
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1.1
  have key : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hPd, Matrix.one_mul]
  set ρ : Mat k r → (H →L[ℂ] H) := fun g => σ (P⁻¹ * g * P) with hρ
  set Sset := {S : Submodule ℂ H | IsKTypeOf ε ρ (Formalism.QuantumDeterminants.lowK ε lam) S} with hSset
  have hmem' : w ∈ ⨆ S : Sset, (S : Submodule ℂ H) := by
    rw [← sSup_eq_iSup']; exact hmem
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 hmem'
  have : ∀ S : Sset, FiniteDimensional ℂ (S : Submodule ℂ H) := fun S => S.2.1
  refine ⟨s.sup fun S : Sset => (S : Submodule ℂ H), ?_, ?_, ?_⟩
  · infer_instance
  · rw [Finset.sup_eq_iSup]; exact hs
  · intro g hg x hx
    have hK : ∀ S : Sset, ∀ y ∈ (S : Submodule ℂ H), σ g y ∈ (S : Submodule ℂ H) := by
      intro S y hy
      have h1 := S.2.2.1 (P * g * P⁻¹) (conj_mem_Kset' hP hg.1 hg.2) y hy
      simpa only [hρ, key] using h1
    clear hs
    induction s using Finset.induction_on generalizing x with
    | empty =>
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert S t hS ih =>
      rw [Finset.sup_insert] at hx ⊢
      obtain ⟨y, hy, y', hy', rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hK S y hy) (ih y' hy')

end Low

end Formalism.MainNotions.KFiniteLowUnitary

end
