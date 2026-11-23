import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreRest
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace ChartFiniteness

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_rename_eq (G : GenFibre v P') (A : MRing ι) :
    aeval G.x' (rename v A) = algebraMap G.Φ G.Φ' (aeval G.x A) := by
  rw [aeval_rename]
  have h : G.x' ∘ v = algebraMap G.Φ G.Φ' ∘ G.x := funext G.compat
  rw [h, MvPolynomial.aeval_algebraMap_apply]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_eq_zero_of_mem (G : GenFibre v P') {f : MRing ι'} (hf : f ∈ P') : aeval G.x' f = 0 := by
  rw [← G.genericFibre_ker_target] at hf
  exact hf

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem aeval_ne_zero_of_not_mem (G : GenFibre v P') {f : MRing ι} (hf : f ∉ imageZ v P') : aeval G.x f ≠ 0 := by
  rw [← G.ker_x] at hf
  exact hf

def coeffPoly {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) : Polynomial F :=
  ∑ j : Fin (m + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)

theorem coeffPoly_coeff_last {F : Type} [Field F] {m : ℕ} (a : Fin (m + 1) → F) :
    (coeffPoly a).coeff m = a (Fin.last m) := by
  unfold coeffPoly
  rw [Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro b _ hb
    have : (m : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext (by simp [h]))
    simp [this]
  · simp

end ChartFiniteness

open ChartFiniteness in

theorem ArithmeticIntersectionChartFinite.of_blockRatioAlg (hR : BlockRatioAlg.Statement) : ArithmeticIntersectionChartFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G j hv hP' hP hj
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨q, rfl⟩
  apply IsAlgebraic.isIntegral
  set c : Σ k', ι' k' := ⟨q.1.1, j q.1⟩ with hc
  have hc0 : G.x' c ≠ 0 := hj q.1
  have hcP : (X c : MRing ι') ∉ P' := by
    intro h
    apply hc0
    have := aeval_eq_zero_of_mem G h
    rwa [aeval_X] at this
  obtain ⟨m, A, a, -, hAm, hmem⟩ := hR K ι K' ι' κ v P' n hv hP' hP ⟨q.1.1, q.2⟩ c rfl hcP
  refine ⟨coeffPoly fun i => aeval G.x (A i), ?_, ?_⟩
  · intro h0
    have := coeffPoly_coeff_last fun i => aeval G.x (A i)
    rw [h0, Polynomial.coeff_zero] at this
    exact aeval_ne_zero_of_not_mem G hAm this.symm
  · have hsum := aeval_eq_zero_of_mem G hmem
    simp only [map_sum, map_mul, map_pow, aeval_X, aeval_rename_eq] at hsum
    have hpow : G.x' c ^ m ≠ 0 := pow_ne_zero _ hc0
    unfold coeffPoly
    simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    apply (mul_left_inj' hpow).mp
    rw [zero_mul, Finset.sum_mul, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.2
    rw [div_pow, mul_assoc, mul_assoc]
    congr 1
    have e : G.x' c ^ m = G.x' c ^ (i : ℕ) * G.x' c ^ (m - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
    rw [e]
    change G.x' _ ^ (i : ℕ) / G.x' c ^ (i : ℕ) * (G.x' c ^ (i : ℕ) * G.x' c ^ (m - i)) = _
    rw [← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hc0)]

theorem ArithmeticIntersectionChartFinite.proof : ArithmeticIntersectionChartFinite.Statement :=
  ArithmeticIntersectionChartFinite.of_blockRatioAlg BlockRatioAlg.proof

end GroundTheory.Heights₂.Heights.Inter
