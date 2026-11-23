import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SepChars
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraBis

open Polynomial Matrix IsLocalRing TensorProduct

private theorem exists_invariant_flag_mod_l {R : Type} [CommRing R] {n : ℕ} (P P' V : Matrix (Fin n) (Fin n) R)
    (hP : ∀ i j, j < i → P i j = 0) (hP' : ∀ i j, j < i → P' i j = 0)
    (hu : ∀ i j, j < i → IsUnit (P i i - P' j j)) (hE : P * V = V * P') :
    ∀ i j, j < i → V i j = 0 := by
  have key : ∀ j i : Fin n, j < i → V i j = 0 := by
    intro j
    induction j using WellFoundedLT.induction with
    | ind j ihj =>
      intro i
      induction i using WellFoundedGT.induction with
      | ind i ihi =>
        intro hji
        have h := congrFun (congrFun hE i) j
        rw [Matrix.mul_apply, Matrix.mul_apply] at h
        have hL : ∑ k, P i k * V k j = P i i * V i j := by
          refine Finset.sum_eq_single i ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [hP i k h1, zero_mul]
          · rw [ihi k h1 (hji.trans h1), mul_zero]
        have hR : ∑ k, V i k * P' k j = V i j * P' j j := by
          refine Finset.sum_eq_single j ?_ (by simp)
          intro k _ hk
          rcases lt_or_gt_of_ne hk with h1 | h1
          · rw [ihj k h1 i (h1.trans hji), zero_mul]
          · rw [hP' k j h1, mul_zero]
        rw [hL, hR] at h
        have h0 : (P i i - P' j j) * V i j = 0 := by
          linear_combination h
        exact ((hu i j hji).mul_right_eq_zero).1 h0
  intro i j h
  exact key j i h

private theorem diag_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) :
    (A * B) i i = A i i * B i i :=
  _root_.UpperTheory.Reformulated.B.S8.diag_mul A B hA hB i

theorem UpperTheory.V.AlgebraTools.flag_chars_unique :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ ψ' : Fin n → Γ →* Rˣ) (g g' : GL (Fin n) R), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ i s, residue R (ψ i s) = residue R (ψ' i s)) → (∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R)) → (∀ s, (∀ i j, j < i → (g' * r s * g'⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g' * r s * g'⁻¹ : GL (Fin n) R) i i = (ψ' i s : R)) → ψ = ψ' ∧ ∀ i j, j < i → (g * g'⁻¹ : GL (Fin n) R) i j = 0 := by
  intro R Γ _ _ _ n r ψ ψ' g g' hn hinj hres h1 h2
  obtain ⟨z, hz⟩ := UpperTheory.V.AlgebraTools.sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hn hinj
  have hcomm : ∀ s, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *
      ((g' * r s * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    intro s
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have key : ∀ w : MonoidAlgebra R Γ, ∃ P P' : Matrix (Fin n) (Fin n) R,
      (∀ i j, j < i → P i j = 0) ∧ (∀ i j, j < i → P' i j = 0) ∧
      P * ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
        ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * P' ∧
      (∀ i, P i i = MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) w) ∧
      (∀ i, residue R (P' i i) = residue R (P i i)) := by
    intro w
    induction w using MonoidAlgebra.induction_on with
    | of s =>
      refine ⟨_, _, (h1 s).1, (h2 s).1, hcomm s, fun i => ?_, fun i => ?_⟩
      · rw [MonoidAlgebra.lift_of]; exact (h1 s).2 i
      · rw [(h1 s).2 i, (h2 s).2 i, hres]
    | add a b ha hb =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      obtain ⟨Q, Q', b1, b2, b3, b4, b5⟩ := hb
      refine ⟨P + Q, P' + Q', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.add_apply, a1 i j h, b1 i j h, add_zero]
      · rw [Matrix.add_apply, a2 i j h, b2 i j h, add_zero]
      · rw [add_mul, mul_add, a3, b3]
      · rw [Matrix.add_apply, map_add, a4, b4]
      · rw [Matrix.add_apply, Matrix.add_apply, map_add, map_add, a5, b5]
    | smul c a ha =>
      obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := ha
      refine ⟨c • P, c • P', fun i j h => ?_, fun i j h => ?_, ?_, fun i => ?_, fun i => ?_⟩
      · rw [Matrix.smul_apply, a1 i j h, smul_zero]
      · rw [Matrix.smul_apply, a2 i j h, smul_zero]
      · rw [Matrix.smul_mul, Matrix.mul_smul, a3]
      · rw [Matrix.smul_apply, map_smul, a4]
      · rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, a5]
  obtain ⟨P, P', a1, a2, a3, a4, a5⟩ := key z
  have hV := exists_invariant_flag_mod_l P P' _ a1 a2 (fun i j h => by
    have hu := hz i j h.ne'
    rw [← a4, ← a4, ← residue_ne_zero_iff_isUnit, map_sub] at hu
    rw [← residue_ne_zero_iff_isUnit, map_sub, a5]
    exact hu) a3
  refine ⟨?_, hV⟩
  have hdet : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  rw [Matrix.det_of_upperTriangular (fun i j h => hV i j h)] at hdet
  funext i
  ext s
  have hu : IsUnit (((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i i) :=
    isUnit_of_dvd_unit (Finset.dvd_prod_of_mem
      (fun k => ((g * g'⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) k k) (Finset.mem_univ i)) hdet
  have h := congrFun (congrFun (hcomm s) i) i
  rw [diag_mul _ _ (h1 s).1 hV, diag_mul _ _ hV (h2 s).1, (h1 s).2 i, (h2 s).2 i, mul_comm] at h
  exact hu.mul_left_cancel h
