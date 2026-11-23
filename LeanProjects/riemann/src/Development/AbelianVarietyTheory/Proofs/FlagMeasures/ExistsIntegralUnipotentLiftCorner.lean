import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
