import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.PosSum

theorem norm_entry_le_trace {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.PosSemidef)
    (i j : Fin N) : ‖A i j‖ ≤ A.trace.re := by
  have hd : ∀ k, 0 ≤ (A k k).re := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).1
  have hi : ∀ k, (A k k).im = 0 := fun k => (Complex.nonneg_iff.1 (hA.diag_nonneg (i := k))).2.symm
  have ht : ∀ k, (A k k).re ≤ A.trace.re := fun k => by
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    exact Finset.single_le_sum (f := fun k => (A k k).re) (fun k _ => hd k) (Finset.mem_univ k)
  have h2 := (Complex.nonneg_iff.1 (hA.submatrix ![i, j]).det_nonneg).1
  have hji : A j i = conj (A i j) := by
    have := hA.1.apply j i
    simpa using this.symm
  rw [Matrix.det_fin_two] at h2
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hji,
    Complex.mul_conj, Complex.sub_re, Complex.mul_re, hi, Complex.ofReal_re, mul_zero, sub_zero,
    Matrix.cons_val_fin_one] at h2
  have h0 : 0 ≤ A.trace.re := (hd i).trans (ht i)
  refine abs_le_of_sq_le_sq' ?_ h0 |>.2
  rw [Complex.sq_norm, sq]
  have := mul_le_mul (ht i) (ht j) (hd j) h0
  linarith

theorem exists_repr_le (E : Type) [Field E] [NumberField E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : 𝓞 E) (j : Module.Free.ChooseBasisIndex ℤ (𝓞 E)),
      |(((RingOfIntegers.basis E).repr x j : ℤ) : ℝ)| ≤ C * house (x : E) := by
  let L := (canonicalEmbedding.latticeBasis E).equivFun.toLinearMap.toContinuousLinearMap
  refine ⟨‖L‖, norm_nonneg _, fun x j => ?_⟩
  have h1 := L.le_opNorm (canonicalEmbedding E x)
  have h2 := norm_le_pi_norm (L (canonicalEmbedding E x)) j
  have h3 : L (canonicalEmbedding E x) j = (((RingOfIntegers.basis E).repr x j : ℤ) : ℂ) := by
    have := canonicalEmbedding.integralBasis_repr_apply E (x : E) j
    rw [NumberField.integralBasis_repr_apply] at this
    simpa [L] using this
  rw [h3, Complex.norm_intCast] at h2
  exact h2.trans h1

theorem house_le_of_isType {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {x : E} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ τ ∈ Ψ, ‖τ x‖ ≤ B) : house x ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB).2 fun τ => ?_
  change ‖τ x‖ ≤ B
  by_cases hτ : τ ∈ Ψ
  · exact h τ hτ
  · have := h _ (not_not.1 fun h' => hτ ((hΨ τ).2 h'))
    simpa using this

end GlobalTheory.SW.PosSum

open GlobalTheory.SW.PosSum in

theorem GlobalTheory.SW.summable_exp_neg_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N c : ℕ) (δ : ℝ), 0 < c → 0 < δ → Summable fun T : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef} => Real.exp (-(δ * ∑ τ : Ψ, (T.1.map τ.1).trace.re)) := by
  intro E _ _ _ Ψ hΨ N c δ hc hδ
  obtain ⟨C, hC, hb⟩ := exists_repr_le E
  let ι := Fin N × Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let K : ℝ := Fintype.card ι * (C * c) + 1
  have hK : 0 < K := by positivity
  let m : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
      ∀ τ : Ψ, (T.map τ.1).PosSemidef} → ι → ℤ := fun T q =>
    (RingOfIntegers.basis E).repr ⟨_, T.2.2.1 q.1 q.2.1⟩ q.2.2
  have hm : Function.Injective m := by
    intro T T' h
    ext a b
    have : (⟨_, T.2.2.1 a b⟩ : 𝓞 E) = ⟨_, T'.2.2.1 a b⟩ :=
      (RingOfIntegers.basis E).ext_elem fun j => congrFun h (a, b, j)
    have h2 : (c : E) * T.1 a b = c * T'.1 a b := congrArg Subtype.val this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hc.ne') h2
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun T => ?_)
    ((GlobalTheory.Koecher.summable_exp_neg_mul_sum_abs (ι := ι) (div_pos hδ hK)).comp_injective hm)
  set S := ∑ τ : Ψ, (T.1.map τ.1).trace.re with hS
  have h0 : ∀ τ : Ψ, 0 ≤ (T.1.map τ.1).trace.re := fun τ =>
    (Complex.nonneg_iff.1 (T.2.2.2 τ).trace_nonneg).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun τ _ => h0 τ
  have hq : ∀ q, |(m T q : ℝ)| ≤ C * c * S := fun q => by
    refine (hb _ _).trans ?_
    change C * house ((c : E) * T.1 q.1 q.2.1) ≤ _
    rw [house_nat_mul, mul_assoc]
    gcongr
    refine house_le_of_isType hΨ hS0 fun τ hτ => ?_
    exact (norm_entry_le_trace (T.2.2.2 ⟨τ, hτ⟩) q.1 q.2.1).trans
      (Finset.single_le_sum (fun τ _ => h0 τ) (Finset.mem_univ (⟨τ, hτ⟩ : Ψ)))
  have hs : ∑ q, |(m T q : ℝ)| ≤ K * S := by
    refine (Finset.sum_le_card_nsmul _ _ _ fun q _ => hq q).trans ?_
    simp only [Finset.card_univ, nsmul_eq_mul, K]
    nlinarith
  simp only [Function.comp_apply]
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  calc δ / K * ∑ q, |(m T q : ℝ)| ≤ δ / K * (K * S) := by gcongr
    _ = δ * S := by field_simp
