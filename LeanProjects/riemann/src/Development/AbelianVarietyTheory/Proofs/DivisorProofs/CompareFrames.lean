import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix

set_option autoImplicit false

namespace GlobalTheory.WholeFlag.Glue.Lattice

variable {K : Type} [Field K]

theorem add_le_max (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) (x y : K) :
    w (x + y) ≤ max (w x) (w y) := by
  have key : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simpa using hab
    · have hb' : 0 < w b := w.pos hb
      have h1 : a / b ∈ O := by
        rw [hO, map_div₀]
        exact (div_le_one hb').2 hab
      have h2 : a / b + 1 ∈ O := O.add_mem _ _ h1 O.one_mem
      rw [hO] at h2
      have h3 : a + b = (a / b + 1) * b := by field_simp
      rw [h3, map_mul]
      calc w (a / b + 1) * w b ≤ 1 * w b := by gcongr
        _ = w b := one_mul _
  rcases le_total (w x) (w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]
    exact (key y x h).trans (le_max_left _ _)

theorem sum_lt_one (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) {ι : Type}
    (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, w (f i) < 1) : w (∑ i ∈ s, f i) < 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (add_le_max w O hO _ _).trans_lt (max_lt (hf a (Finset.mem_insert_self _ _)) (ih ?_))
    intro i hi
    exact hf i (Finset.mem_insert_of_mem hi)

theorem inv_le_one (w : AbsoluteValue K ℝ) (O : ValuationSubring K) (hO : ∀ x, x ∈ O ↔ w x ≤ 1) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ r c, w (M r c) ≤ 1) (hd : w M.det = 1) (r c : Fin n) :
    w (M⁻¹ r c) ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨M i j, (hO _).2 (hM i j)⟩
  have hM' : O.subtype.mapMatrix M' = M := by
    ext i j
    rfl
  have hadj : M.adjugate r c = (M'.adjugate r c : K) := by
    rw [← hM', ← RingHom.map_adjugate]
    rfl
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv', map_inv₀, hd, inv_one, one_mul,
    hadj]
  exact (hO _).1 (M'.adjugate r c).2

theorem compare_frames : ∀ {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K), (∀ x, x ∈ O ↔ w x ≤ 1) → ∀ {g : ℕ} (Ha Hb : Matrix (Fin (g + g)) (Fin g) K) (βa βb : Matrix (Fin g) (Fin g) K) (τa τb : Fin g → Fin (g + g)) (Ma : Matrix (Fin (g + g)) (Fin (g + g)) K), βa.BlockTriangular id → βb.BlockTriangular id → (∀ k, βa k k ≠ 0) → (∀ k, βb k k ≠ 0) → (∀ r k, w ((Ha * βa) r k) ≤ 1) → (∀ r k, w ((Hb * βb) r k) ≤ 1) → w (rowSel τa * (Ha * βa)).det = 1 → w (rowSel τb * (Hb * βb)).det = 1 → (∀ u, (∀ r, w ((Ha *ᵥ u) r) ≤ 1) → ∀ r, w ((Hb *ᵥ u) r - (Ha *ᵥ u) r) < 1) → (∀ u, (∀ r, w ((Hb *ᵥ u) r) ≤ 1) → ∀ r, w ((Ha *ᵥ u) r - (Hb *ᵥ u) r) < 1) → (∀ r c, w (Ma r c) ≤ 1) → w Ma.det = 1 → (∀ r (k : Fin g), Ma r (Fin.castAdd g k) = (Ha * βa) r k) → ∀ (k : Fin g) (i : Fin (g + g)), ((k : ℕ) < i → w ((Ma⁻¹ * (Hb * βb)) i k) < 1) ∧ w ((Ma⁻¹ * (Hb * βb)) (Fin.castAdd g k) k - βb k k / βa k k) < 1 := by
  intro K _ w O hO g Ha Hb βa βb τa τb Ma hta htb hda _ _ hB _ _ _ h2 hMa hdet hcol k i
  have hdetβ : IsUnit βa.det := by
    rw [Matrix.det_of_upperTriangular hta, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hda j
  have hdetM : IsUnit Ma.det := by
    rw [isUnit_iff_ne_zero]
    intro h
    rw [h] at hdet
    simp at hdet
  letI : Invertible βa := βa.invertibleOfIsUnitDet hdetβ
  set Q : Matrix (Fin g) (Fin g) K := βa⁻¹ * βb with hQ
  have hQt : Q.BlockTriangular id := (Matrix.blockTriangular_inv_of_blockTriangular hta).mul htb
  have hβQ : βa * Q = βb := by
    rw [hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetβ, Matrix.one_mul]
  have hQd : Q k k = βb k k / βa k k := by
    rw [eq_div_iff (hda k), ← hβQ, Matrix.mul_apply, Finset.sum_eq_single k, mul_comm]
    · intro j _ hj
      rcases lt_or_gt_of_ne hj with h | h
      · rw [hta (show id j < id k from h), zero_mul]
      · rw [hQt (show id k < id j from h), mul_zero]
    · simp
  let E : Matrix (Fin (g + g)) (Fin g) K := Matrix.of fun r j => if r = Fin.castAdd g j then 1 else 0
  have hME : Ma * E = Ha * βa := by
    ext r j
    rw [← hcol, Matrix.mul_apply]
    simp [E]
  have hC : Ma⁻¹ * (Ha * βb) = E * Q := by
    rw [← hβQ, ← Matrix.mul_assoc Ha, ← hME, Matrix.mul_assoc Ma E Q, ← Matrix.mul_assoc Ma⁻¹ Ma,
      Matrix.nonsing_inv_mul _ hdetM, Matrix.one_mul]
  have hD : ∀ r, w ((Hb * βb - Ha * βb) r k) < 1 := by
    intro r
    have h := h2 (fun j => βb j k) (fun r' => hB r' k) r
    rw [w.map_sub] at h
    exact h
  have hdiff : ∀ r, w ((Ma⁻¹ * (Hb * βb)) r k - (E * Q) r k) < 1 := by
    intro r
    rw [← hC, ← Matrix.sub_apply, ← Matrix.mul_sub, Matrix.mul_apply]
    refine sum_lt_one w O hO _ _ fun j _ => ?_
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (inv_le_one w O hO Ma hMa hdet r j) (w.nonneg _) (hD j)
  refine ⟨fun hki => ?_, ?_⟩
  · have h0 : (E * Q) i k = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hij : i = Fin.castAdd g j
      · subst hij
        rw [hQt (show id k < id j from hki), mul_zero]
      · simp [E, hij]
    have h := hdiff i
    rwa [h0, sub_zero] at h
  · have h0 : (E * Q) (Fin.castAdd g k) k = βb k k / βa k k := by
      rw [← hQd, Matrix.mul_apply, Finset.sum_eq_single k]
      · simp [E]
      · intro j _ hj
        have : Fin.castAdd g k ≠ Fin.castAdd g j := fun h => hj (Fin.castAdd_injective _ _ h).symm
        simp [E, this]
      · simp
    have h := hdiff (Fin.castAdd g k)
    rwa [h0] at h

end GlobalTheory.WholeFlag.Glue.Lattice
