import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUnitOfSumEqOne

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell

theorem det_mem_subring {F : Type} [CommRing F] (D : Subring F) {k : ℕ} (A : Matrix (Fin k) (Fin k) F)
    (hA : ∀ a b, A a b ∈ D) : A.det ∈ D := by
  rw [Matrix.det_apply']
  exact D.sum_mem fun σ _ => D.mul_mem (intCast_mem D _) (D.prod_mem fun a _ => hA _ _)

theorem mul_adjugate_apply_eq_kMinor {F : Type} [Field F] {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F) (m : ℕ)
    (hm : m ≤ r) (J : Fin m → Fin n) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      kMinor Y m hm (Function.update J j i) := by
  classical
  have h1 : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm)).adjugate) i j =
      Matrix.cramer (Y.submatrix J (Fin.castLE hm)).transpose (Y.submatrix id (Fin.castLE hm) i) j := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← Matrix.adjugate_transpose]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h1, Matrix.cramer_transpose_apply]
  unfold kMinor
  congr 1
  ext a b
  by_cases hab : a = j
  · subst hab
    simp
  · simp [Matrix.updateRow_ne hab, Function.update_of_ne hab]

theorem normAt_mul_inv_mem {F : Type} [Field F] (O : Subring F) {n r : ℕ} (Y : Matrix (Fin n) (Fin r) F)
    (m : ℕ) (hm : m ≤ r) (J : Fin m → Fin n) (hJ : NormAt O Y m hm J) (i : Fin n) (j : Fin m) :
    (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j ∈ O := by
  classical
  have e : (Y.submatrix id (Fin.castLE hm) * (Y.submatrix J (Fin.castLE hm))⁻¹) i j =
      kMinor Y m hm (Function.update J j i) / kMinor Y m hm J := by
    rw [Matrix.inv_def, Matrix.mul_smul, Matrix.smul_apply, mul_adjugate_apply_eq_kMinor,
      Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]
    rfl
  rw [e]
  exact hJ.2 _

theorem normAt_exchange {F : Type} [Field F] (O : Subring F) [IsLocalRing O] {n r : ℕ}
    (Y : Matrix (Fin n) (Fin r) F) (k : ℕ) (hk : k + 1 ≤ r) (I' : Fin (k + 1) → Fin n) (I : Fin k → Fin n)
    (h' : NormAt O Y (k + 1) hk I') (h : NormAt O Y k (Nat.le_of_succ_le hk) I) :
    ∃ f : Fin k → Fin (k + 1), Function.Injective f ∧ NormAt O Y k (Nat.le_of_succ_le hk) (I' ∘ f) := by
  classical
  have hk0 : k ≤ r := Nat.le_of_succ_le hk
  have hM' : IsUnit (Y.submatrix I' (Fin.castLE hk)).det := isUnit_iff_ne_zero.2 h'.1
  have hM : IsUnit (Y.submatrix I (Fin.castLE hk0)).det := isUnit_iff_ne_zero.2 h.1
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = Y.submatrix id (Fin.castLE hk) * (Y.submatrix I' (Fin.castLE hk))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z', Z' = Y.submatrix id (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ :=
    ⟨_, rfl⟩
  have hZ : ∀ a b, Z a b ∈ O := fun a b => by
    rw [hZdef]; exact normAt_mul_inv_mem O Y _ hk I' h' a b
  have hZ' : ∀ a b, Z' a b ∈ O := fun a b => by
    rw [hZ'def]; exact normAt_mul_inv_mem O Y _ hk0 I h a b
  have e1 : Y.submatrix id (Fin.castLE hk) = Z * Y.submatrix I' (Fin.castLE hk) := by
    rw [hZdef, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hM', Matrix.mul_one]
  have hY0 : Y.submatrix id (Fin.castLE hk0) = Z * (Y.submatrix I' (Fin.castLE hk0)) := by
    ext a b
    have := congrFun (congrFun e1 a) (Fin.castSucc b)
    simpa [Matrix.mul_apply] using this
  have hD : ∀ {m : ℕ} (J : Fin m → Fin n), Z'.submatrix J id =
      Y.submatrix J (Fin.castLE hk0) * (Y.submatrix I (Fin.castLE hk0))⁻¹ := by
    intro m J
    rw [hZ'def]
    ext a b
    simp [Matrix.mul_apply]
  have hZZ : Z' = Z * Z'.submatrix I' id := by
    rw [hD, ← Matrix.mul_assoc, ← hY0, hZ'def]
  have hI : Z'.submatrix I id = 1 := by
    rw [hD, Matrix.mul_nonsing_inv _ hM]
  have hone : Z.submatrix I id * Z'.submatrix I' id = 1 := by
    rw [← hI]
    conv_rhs => rw [hZZ]
    ext a b
    simp [Matrix.mul_apply]
  have hsum := det_mul_expand (Z.submatrix I id) (Z'.submatrix I' id)
  rw [hone, Matrix.det_one] at hsum
  obtain ⟨f, -, hne, hinv⟩ := exists_unit_of_sum_eq_one O Finset.univ _
    (fun f _ => O.mul_mem (O.prod_mem fun a _ => hZ _ _) (det_mem_subring O _ fun a b => hZ' _ _)) hsum.symm
  have hc : (∏ a, (Z.submatrix I id) a (f a)) ≠ 0 := left_ne_zero_of_mul hne
  have hd : ((Z'.submatrix I' id).submatrix f id).det ≠ 0 := right_ne_zero_of_mul hne
  have hdet : ((Z'.submatrix I' id).submatrix f id).det =
      kMinor Y k hk0 (I' ∘ f) / kMinor Y k hk0 I := by
    have e2 : (Z'.submatrix I' id).submatrix f id = Z'.submatrix (I' ∘ f) id := by
      ext a b; simp
    rw [e2, hD, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', div_eq_mul_inv]
    rfl
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne'
    exact hd (Matrix.det_zero_of_row_eq hne' (by ext c; simp [hab]))
  refine ⟨f, hinj, ?_, fun I'' => ?_⟩
  · intro h0
    apply hd
    rw [hdet, h0, zero_div]
  · have hP := h.1
    have hQ : kMinor Y k hk0 (I' ∘ f) ≠ 0 := by
      intro h0
      apply hd
      rw [hdet, h0, zero_div]
    have e : kMinor Y k hk0 I'' / kMinor Y k hk0 (I' ∘ f) =
        (kMinor Y k hk0 I'' / kMinor Y k hk0 I) * ((∏ a, (Z.submatrix I id) a (f a)) *
          ((∏ a, (Z.submatrix I id) a (f a)) * ((Z'.submatrix I' id).submatrix f id).det)⁻¹) := by
      rw [hdet]
      field_simp
    rw [e]
    exact O.mul_mem (h.2 I'') (O.mul_mem (O.prod_mem fun a _ => hZ _ _) hinv)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell
