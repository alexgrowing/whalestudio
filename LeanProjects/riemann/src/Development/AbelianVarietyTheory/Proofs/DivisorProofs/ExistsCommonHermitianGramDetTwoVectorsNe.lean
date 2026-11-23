import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

theorem hE_add_smul_right (z u v : Fin M → E) (c : E) :
    hE σ J z (u + c • v) = hE σ J z u + c * hE σ J z v := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_left (z u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) z = hE σ J u z + σ c * hE σ J v z := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hE_add_smul_self (u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) (u + c • v) =
      hE σ J u u + c * hE σ J u v + σ c * hE σ J v u + σ c * c * hE σ J v v := by
  rw [hE, GlobalTheory.HermLineZeros.hform_expand]
  rfl

theorem hE_single (i j : Fin M) : hE σ J (Pi.single i 1) (Pi.single j 1) = J i j :=
  GlobalTheory.HermLineZeros.hform_single _ J i j

theorem hermitianGramDetTwoVectors_comm (x z : Fin M → E) : gram2E σ J x z = gram2E σ J z x := by
  unfold gram2E; ring

noncomputable def gramPoly (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (z a b : Fin M → E) : Polynomial E :=
  Polynomial.C (hE σ J z z) * (Polynomial.C (hE σ J a a) + Polynomial.X * Polynomial.C (hE σ J a b + hE σ J b a)
      + Polynomial.X ^ 2 * Polynomial.C (hE σ J b b))
    - (Polynomial.C (hE σ J z a) + Polynomial.X * Polynomial.C (hE σ J z b))
      * (Polynomial.C (hE σ J a z) + Polynomial.X * Polynomial.C (hE σ J b z))

theorem hermitianGramDetTwoVectors_eval_line (z a b : Fin M → E) (t : E) (ht : σ t = t) :
    gram2E σ J z (a + t • b) = (gramPoly σ J z a b).eval t := by
  unfold gram2E gramPoly
  rw [hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

section CM

variable [NumberField F] [NumberField E]

theorem exists_gram2E_ne (h : IsCMExt F E σ) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    (z : Fin M → E) (hz : hE σ J z z ≠ 0) : ∃ w, gram2E σ J z w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z
  set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)
  have hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0 := fun i => by
    have := hc (Pi.single i 1)
    simpa [gram2E, hE_single] using this
  have key : hE σ J z z • J = Matrix.vecMulVec a b := by
    ext i j
    have e1 := hc (Pi.single i 1 + (1 : E) • Pi.single j 1)
    have e2 := hc (Pi.single i 1 + d • Pi.single j 1)
    simp only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single,
      map_one] at e1 e2
    have e0i := hdiag i
    have e0j := hdiag j
    have : (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0 := by
      simp only [a, b] at e0i e0j ⊢
      linear_combination e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hd
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      exact sub_eq_zero.1 h0
  have hdet : (hE σ J z z • J).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hJ.2
  have hunit : IsUnit (hE σ J z z • J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hr := Matrix.rank_of_isUnit _ hunit
  have hle : (Matrix.vecMulVec a b).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  rw [key, Fintype.card_fin] at hr
  omega

end CM

end GlobalTheory.GramVec

open GlobalTheory.GramVec in
theorem GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  intro F E _ _ _ _ _ σ h M J hM hJ x y hx hy
  obtain ⟨w0, h0⟩ := exists_gram2E_ne h hM hJ x hx
  obtain ⟨w1, h1⟩ := exists_gram2E_ne h hM hJ y hy
  set Px := gramPoly σ J x w0 (w1 - w0)
  set Py := gramPoly σ J y w0 (w1 - w0)
  have hPx : Px ≠ 0 := by
    intro h0'
    apply h0
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)
    rw [zero_smul, add_zero] at this
    rw [this]; change Polynomial.eval 0 Px = 0; rw [h0', Polynomial.eval_zero]
  have hPy : Py ≠ 0 := by
    intro h1'
    apply h1
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)
    rw [one_smul, add_sub_cancel] at this
    rw [this]; change Polynomial.eval 1 Py = 0; rw [h1', Polynomial.eval_zero]
  have hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite := by
    have := ((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage
      (FaithfulSMul.algebraMap_injective F E).injOn
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨f, hf⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf
  have hfix : σ (algebraMap F E f) = algebraMap F E f := σ.commutes f
  refine ⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩
  · rw [hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.1
  · rw [hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.2
