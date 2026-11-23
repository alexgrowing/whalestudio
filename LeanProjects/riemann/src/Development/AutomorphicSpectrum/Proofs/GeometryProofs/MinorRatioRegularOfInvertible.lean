import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

theorem mul_inv_apply_eq_det_div {K : Type} [Field K] {n r m : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (J : Fin m → Fin n) (c : Fin m → Fin r) (j : Fin n) (l : Fin m) :
    ((F.submatrix id c) * (F.submatrix J c)⁻¹) j l =
      (F.submatrix (Function.update J l j) c).det / (F.submatrix J c).det := by
  have hrow : F.submatrix (Function.update J l j) c =
      (F.submatrix J c).updateRow l (fun k => F j (c k)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply, Function.update_apply]
    split_ifs <;> rfl
  have key : (F.submatrix (Function.update J l j) c).det =
      ∑ k, F j (c k) * (F.submatrix J c).adjugate k l := by
    rw [hrow, ← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, Matrix.mul_apply, Matrix.inv_def, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  ring

theorem split_of_regular_ratios (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K)
    (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r)
    (J : Fin ((k : ℕ) + 1) → Fin n) (hA : ∀ j l, A j l ∈ R) (hB : ∀ l j, B l j ∈ R) (hBA : B * A = 1)
    (_ha : a ≠ 0) (hdet : ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0)
    (hR : ∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det /
      ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) :
    ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧
      ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  have hN' : (a • (A * G)).submatrix id (Fin.castLE k.2) = A * (a • G.submatrix id (Fin.castLE k.2)) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.mul_apply, id_eq, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r) (Fin ((k : ℕ) + 1)) K,
      Q = (a • G.submatrix id (Fin.castLE k.2)) * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ :=
    ⟨_, rfl⟩
  have hAQ : A * Q = (a • (A * G)).submatrix id (Fin.castLE k.2) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ := by
    rw [hQ, ← Matrix.mul_assoc, ← hN']
  have hBQ : Q = B * (A * Q) := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hPR : ∀ j l, (A * Q) j l ∈ R := by
    intro j l
    rw [hAQ, mul_inv_apply_eq_det_div]
    exact hR l j
  refine ⟨fun l i => Q i l, fun l i => A (J l) i, ?_, ?_, ?_, ?_⟩
  · intro l i
    show Q i l ∈ R
    rw [hBQ, Matrix.mul_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hB i j) (hPR j l)
  · intro l i
    exact hA (J l) i
  · intro l l'
    change (A * Q) (J l) l' = _
    rw [hAQ]
    change (((a • (A * G)).submatrix J (Fin.castLE k.2)) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹) l l' = _
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]
  · intro l
    have hD : (fun i => Q i l) = ∑ c : Fin ((k : ℕ) + 1),
        (a * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ c l) • (fun i => G i (Fin.castLE k.2 c)) := by
      funext i
      rw [hQ]
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul,
        Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun c _ => by ring
    show (fun i => Q i l) ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1)
    rw [hD]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_image_of_mem (fun c i => G i c)
        (show (Fin.castLE k.2 c : Fin r) ∈ {c' : Fin r | (c' : ℕ) < (k : ℕ) + 1} from c.2)))

end GlobalTheory.CompanionTheory.Ar.FlagBun
