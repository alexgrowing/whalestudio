import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.LogDetSt

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorJet

section Linfty
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_exp_entry {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (i j : Fin n) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((u : ℂ) • Y) i j)
      ((NormedSpace.exp ((s : ℂ) • Y) * Y) i j) s := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y s
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt s h
  simp only [Complex.coe_smul]
  exact h2

end Linfty

theorem hasDerivAt_mul_entry {r : ℕ} (G H : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (G' H' : Matrix (Fin r) (Fin r) ℂ) (t : ℝ)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (H' i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s * H s) i j) ((G' * H t + G t * H') i j) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hG i k).fun_mul (hH k j))
  simpa [Matrix.mul_apply, Matrix.add_apply, Finset.sum_add_distrib] using h

theorem hasDerivAt_adjugate_entry {r : ℕ} (G : ℝ → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ) (t : ℝ) (h0 : G t = 1)
    (hG : ∀ i j, HasDerivAt (fun s => G s i j) (A i j) t) (i j : Fin r) :
    HasDerivAt (fun s => (G s).adjugate i j) ((A.trace • (1 : Matrix (Fin r) (Fin r) ℂ) - A) i j) t := by
  have hP : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b)
      ((((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace) t := by
    intro a b
    have hrow : ∀ p q, HasDerivAt (fun s => (G s).updateRow b (Pi.single a 1) p q)
        ((A.updateRow b 0) p q) t := by
      intro p q
      by_cases hp : p = b
      · subst hp
        simp only [updateRow_self]
        exact hasDerivAt_const _ _
      · simp only [updateRow_ne hp]
        exact hG p q
    have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun s => (G s).updateRow b (Pi.single a 1)) _ t hrow
    simpa only [adjugate_apply] using h
  let D : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b =>
    (((G t).updateRow b (Pi.single a 1)).adjugate * A.updateRow b 0).trace
  have hD : ∀ a b, HasDerivAt (fun s => (G s).adjugate a b) (D a b) t := fun a b => hP a b
  have h1 := hasDerivAt_mul_entry (fun s => (G s).adjugate) G D A t hD hG i j
  have h2 := (ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det G A t hG).mul_const ((1 : Matrix (Fin r) (Fin r) ℂ) i j)
  have h3 : HasDerivAt (fun s => (G s).det * (1 : Matrix (Fin r) (Fin r) ℂ) i j)
      ((D * G t + (G t).adjugate * A) i j) t := by
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hu := h3.unique h2
  rw [h0, adjugate_one, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply] at hu
  have hDij : D i j = A.trace * (1 : Matrix (Fin r) (Fin r) ℂ) i j - A i j := by
    linear_combination hu
  convert hD i j using 1
  rw [hDij, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]

private theorem sum_castLE_lemma {n l : ℕ} (hl : l ≤ n) (f : Fin n → ℂ) :
    ∑ x : Fin l, f (Fin.castLE hl x) = ∑ a : Fin n, if a.val < l then f a else 0 := by
  have e : (Finset.univ : Finset (Fin l)).map (Fin.castLEEmb hl) =
      Finset.univ.filter (fun a : Fin n => a.val < l) := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨x, rfl⟩
      simp
    · intro h
      exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  rw [← Finset.sum_filter, ← e, Finset.sum_map]
  rfl

theorem trace_block {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian) (l : ℕ) (hl : l ≤ n) :
    ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace -
      (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
    ((∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 : ℝ) : ℂ) := by
  have hH : ∀ a b, Y a b * Y b a = ((‖Y b a‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have e : Y a b = star (Y b a) := by
      have := congrFun (congrFun hY a) b
      rw [conjTranspose_apply] at this
      exact this.symm
    rw [e, Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e1 : ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.mul_apply]
    exact sum_castLE_lemma hl (fun a => ∑ b : Fin n, Y a b * Y b a)
  have e2 : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) *
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
      ∑ a : Fin n, if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.submatrix_apply]
    rw [← sum_castLE_lemma hl (fun a => ∑ b : Fin n, if b.val < l then Y a b * Y b a else 0)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact sum_castLE_lemma hl (fun b => Y (Fin.castLE hl x) b * Y b (Fin.castLE hl x))
  have key : ∀ a : Fin n, ((if a.val < l then ∑ b : Fin n, Y a b * Y b a else 0) -
      (if a.val < l then ∑ b : Fin n, (if b.val < l then Y a b * Y b a else 0) else 0)) =
      ∑ b : Fin n, ((if l ≤ b.val ∧ a.val < l then ‖Y b a‖ ^ 2 else 0 : ℝ) : ℂ) := by
    intro a
    by_cases ha : a.val < l
    · rw [if_pos ha, if_pos ha, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      by_cases hb : b.val < l
      · rw [if_pos hb, if_neg (fun h => absurd h.1 (Nat.not_le.mpr hb)), sub_self,
          Complex.ofReal_zero]
      · rw [if_neg hb, sub_zero, if_pos ⟨Nat.le_of_not_lt hb, ha⟩, hH]
    · rw [if_neg ha, if_neg ha, sub_self]
      symm
      refine Finset.sum_eq_zero (fun b _ => ?_)
      rw [if_neg (fun h => ha h.2), Complex.ofReal_zero]
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun a _ => key a), Finset.sum_comm,
    Complex.ofReal_sum]
  simp only [Complex.ofReal_sum]

theorem deriv_leadMinor_exp : ∀ (n : ℕ) (Y : Matrix (Fin n) (Fin n) ℂ), Y.IsHermitian → (∀ a, Y a a = 0) → ∀ (l : ℕ) (hl : l ≤ n), deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) 0 = 0 ∧ deriv (deriv (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)) 0 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
  intro n Y hY hdiag l hl
  have hE0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have hM0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) = 1 := by
    rw [hE0]
    exact submatrix_one _ (Fin.castLE_injective hl)
  have hM'0 : (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Y.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    rw [hE0, Matrix.one_mul]
  have htr : (Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace = 0 := by
    simp [Matrix.trace, hdiag]
  have hM : ∀ (t : ℝ) x y, HasDerivAt
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
      ((NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) t :=
    fun t x y => hasDerivAt_exp_entry Y t (Fin.castLE hl x) (Fin.castLE hl y)
  have hf : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re)
      (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re t := by
    intro t
    have hg := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det
      (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ t (hM t)
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
    simpa [leadMinor, Function.comp_def] using h
  have hderiv : deriv (fun s : ℝ => (leadMinor (NormedSpace.exp ((s : ℂ) • Y)) l hl).re) =
      fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
        (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re :=
    funext fun t => (hf t).deriv
  rw [hderiv]
  refine ⟨?_, ?_⟩
  · beta_reduce
    rw [hM0, hM'0, adjugate_one, Matrix.one_mul, htr, Complex.zero_re]
  · have hadj : ∀ x y, HasDerivAt
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate x y)
        (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) -
          Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) x y) 0 := by
      intro x y
      have h := hasDerivAt_adjugate_entry
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)) _ 0 hM0
        (hM 0) x y
      rwa [hM'0] at h
    have hMd : ∀ x y, HasDerivAt
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y)
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) x y) 0 := by
      intro x y
      have h := hasDerivAt_mul_entry (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) (fun _ => Y)
        (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y) 0 0 (hasDerivAt_exp_entry Y 0)
        (fun _ _ => hasDerivAt_const _ _) (Fin.castLE hl x) (Fin.castLE hl y)
      rw [hE0, Matrix.one_mul, Matrix.mul_zero, add_zero] at h
      exact h
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
      hasDerivAt_mul_entry
        (fun s : ℝ => ((NormedSpace.exp ((s : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate)
        (fun s : ℝ => (NormedSpace.exp ((s : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl))
        _ _ 0 hadj hMd x x)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hsum
    have h3 : HasDerivAt
        (fun t : ℝ => (((NormedSpace.exp ((t : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (NormedSpace.exp ((t : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace.re)
        ((((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace).re 0 := h2
    have hv : (((Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace • (1 : Matrix (Fin l) (Fin l) ℂ) - Y.submatrix (Fin.castLE hl) (Fin.castLE hl)) *
          (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * Y).submatrix (Fin.castLE hl) (Fin.castLE hl) +
          ((NormedSpace.exp (((0 : ℝ) : ℂ) • Y)).submatrix (Fin.castLE hl) (Fin.castLE hl)).adjugate *
          (Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace =
        ((Y * Y).submatrix (Fin.castLE hl) (Fin.castLE hl)).trace - (Y.submatrix (Fin.castLE hl) (Fin.castLE hl) * Y.submatrix (Fin.castLE hl) (Fin.castLE hl)).trace := by
      rw [hM0, hM'0, adjugate_one, htr, zero_smul, zero_sub, Matrix.neg_mul, Matrix.one_mul,
        Matrix.trace_add, Matrix.trace_neg]
      ring
    rw [h3.deriv, hv, trace_block Y hY l hl, Complex.ofReal_re]

end GlobalTheory.MinorJet
