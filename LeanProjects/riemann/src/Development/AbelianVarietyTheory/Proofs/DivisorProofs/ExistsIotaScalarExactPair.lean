import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.ScalarEx

theorem det_add_rows {C : Type} [Field C] {N : ℕ} (S : Fin N → Prop) [DecidablePred S]
    (W : Submodule C (Fin N → C)) (hW : Module.finrank C W = Fintype.card {i // S i})
    (r s : Fin N → Fin N → C) (hr : ∀ i, S i → r i ∈ W) (hd0 : ∀ i, S i → s i = r i)
    (hd : ∀ i, ¬ S i → s i - r i ∈ W) :
    (Matrix.of s).det = (Matrix.of r).det := by
  classical
  by_cases hli : LinearIndependent C (fun i : {i // S i} => r i)
  · have hspan : Submodule.span C (Set.range (fun i : {i // S i} => r i)) = W := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hr i i.2
      · rw [finrank_span_eq_card hli, hW]
    have hc : ∀ j, ∃ c : {i // S i} → C, (S j → c = 0) ∧ ∑ i, c i • r i = s j - r j := by
      intro j
      by_cases hj : S j
      · exact ⟨0, fun _ => rfl, by simp [hd0 j hj]⟩
      · have h1 := hd j hj
        rw [← hspan] at h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 h1
        exact ⟨c, fun h => absurd h hj, hc⟩
    choose c hc0 hc using hc
    let Q : Matrix {i // S i} (Fin N) C := Matrix.of fun i l => if i.1 = l then 1 else 0
    have hQ : ∀ {κ : Type} (M : Matrix (Fin N) κ C) (i : {i // S i}) (k : κ),
        (Q * M) i k = M i k := by
      intro κ M i k
      simp [Q, Matrix.mul_apply]
    have h1 : Matrix.of s = (1 + Matrix.of c * Q) * Matrix.of r := by
      ext j k
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.add_apply, Matrix.mul_apply]
      have h2 := congrFun (hc j) k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h2
      simp only [hQ, Matrix.of_apply, h2]
      ring
    have h2 : Q * Matrix.of c = 0 := by
      ext i k
      rw [hQ]
      simp [hc0 i.1 i.2]
    rw [h1, Matrix.det_mul, Matrix.det_one_add_mul_comm, h2]
    simp
  · have h1 : (Matrix.of r).det = 0 := by
      by_contra h
      exact hli ((Matrix.linearIndependent_rows_of_det_ne_zero h).comp _ Subtype.val_injective)
    have h2 : (Matrix.of s).det = 0 := by
      by_contra h
      have h3 := (Matrix.linearIndependent_rows_of_det_ne_zero h).comp _
        (Subtype.val_injective (p := S))
      apply hli
      have h4 : (fun i : {i // S i} => r i) = (fun i => Matrix.of s i) ∘ Subtype.val :=
        funext fun i => (hd0 i.1 i.2).symm
      rw [h4]
      exact h3
    rw [h1, h2]

theorem exists_ginv {C V : Type} [Field C] [AddCommGroup V] [Module C V] (f : V →ₗ[C] V) :
    ∃ g : V →ₗ[C] V, ∀ z, f (g (f z)) = f z := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ t, fun z => ?_⟩
  have h1 : t (f z) = f.rangeRestrict z := LinearMap.congr_fun ht (f.rangeRestrict z)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict z))
  rw [LinearMap.comp_apply, h1]
  exact h2

theorem card_lt {N a : ℕ} (h : a ≤ N) : Fintype.card {i : Fin N // (i : ℕ) < a} = a := by
  rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  exact min_eq_right h

theorem exists_iotaScalar (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C)
    (hab : α * β = 0) (hba : β * α = 0) (hex : ∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) :
    ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  classical
  set U : Submodule C (Fin N → C) := LinearMap.range β.mulVecLin with hUdef
  have hU : Module.finrank C U = β.rank := rfl
  have haN : β.rank ≤ N := by simpa using Matrix.rank_le_width β
  have hUker : ∀ z, z ∈ U ↔ α *ᵥ z = 0 := by
    intro z
    constructor
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hab]
    · intro h
      obtain ⟨y, rfl⟩ := hex z h
      exact ⟨y, rfl⟩
  have hker : LinearMap.ker α.mulVecLin = U := by
    ext z
    rw [hUker]; simp
  have hkerβ : LinearMap.range α.mulVecLin = LinearMap.ker β.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hba]
    · have h1 := LinearMap.finrank_range_add_finrank_ker α.mulVecLin
      have h2 := LinearMap.finrank_range_add_finrank_ker β.mulVecLin
      rw [hker] at h1
      rw [← hUdef] at h2
      omega
  obtain ⟨F, hF⟩ := Submodule.exists_isCompl U
  have hFr : Module.finrank C F = Fintype.card {i : Fin N // ¬ (i : ℕ) < β.rank} := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hF
    rw [Fintype.card_subtype_compl, card_lt haN]
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨q, hqF, hqU⟩ : ∃ q : (Fin N → C) →ₗ[C] (Fin N → C),
      (∀ z, q z ∈ F) ∧ ∀ z, z - q z ∈ U := by
    refine ⟨F.subtype ∘ₗ F.projectionOnto U hF.symm, fun z => Subtype.prop _, fun z => ?_⟩
    refine (Submodule.ker_projectionOnto hF.symm).le ?_
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.projectionOnto_apply_left, sub_self]
  obtain ⟨g, hg⟩ := exists_ginv α.mulVecLin
  simp only [Matrix.mulVecLin_apply] at hg
  let Θ : (Fin N → C) →ₗ[C] (Fin N → C) := β.mulVecLin + q ∘ₗ g
  have hΘ : ∀ z, Θ z = β *ᵥ z + q (g z) := fun z => rfl
  have hq : ∀ z, α *ᵥ q z = α *ᵥ z := by
    intro z
    have h1 := (hUker _).1 (hqU z)
    rw [Matrix.mulVec_sub, sub_eq_zero] at h1
    exact h1.symm
  have hΘα : ∀ z, Θ (α *ᵥ z) = q (g (α *ᵥ z)) := by
    intro z
    rw [hΘ, Matrix.mulVec_mulVec, hba, Matrix.zero_mulVec, zero_add]
  let M := LinearMap.toMatrix' Θ
  have hM : ∀ z, M *ᵥ z = Θ z := fun z => LinearMap.toMatrix'_mulVec Θ z
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hz
    rw [hM] at h0
    have h1 : β *ᵥ z ∈ F := by
      have h2 : β *ᵥ z = - q (g z) := eq_neg_of_add_eq_zero_left (by rw [← hΘ, h0])
      rw [h2]; exact F.neg_mem (hqF _)
    have h2 : β *ᵥ z = 0 := (Submodule.disjoint_def.1 hF.disjoint) _ ⟨z, rfl⟩ h1
    have h3 : z ∈ LinearMap.range α.mulVecLin := by rw [hkerβ]; exact h2
    obtain ⟨w, rfl⟩ := h3
    simp only [Matrix.mulVecLin_apply] at h0 ⊢
    rw [← hg, ← hq, ← hΘα, h0, Matrix.mulVec_zero]
  refine ⟨M.det⁻¹, inv_ne_zero hdet, fun x y hx hy => ?_⟩
  let m : Fin N → Fin N → C := fun i => if (i : ℕ) < β.rank then x i else Θ (y i)
  have h1 : (Matrix.of x).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => (i : ℕ) < β.rank) U (by rw [card_lt haN, hU]) m x ?_ ?_ ?_
    · intro i hi
      simp only [m, if_pos hi]
      exact ⟨y i, (hx i hi).symm⟩
    · intro i hi
      simp only [m, if_pos hi]
    · intro i hi
      simp only [m, if_neg hi]
      rw [hUker, hy i (not_lt.1 hi), hΘα, Matrix.mulVec_sub, hq, hg, sub_self]
  have h2 : (Matrix.of fun i => Θ (y i)).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => ¬ (i : ℕ) < β.rank) F hFr m _ ?_ ?_ ?_
    · intro i hi
      simp only [m, if_neg hi]
      rw [hy i (not_lt.1 hi), hΘα]
      exact hqF _
    · intro i hi
      simp only [m, if_neg hi]
    · intro i hi
      have hi' := not_not.1 hi
      simp only [m, if_pos hi']
      rw [hΘ, hx i hi', add_sub_cancel_left]
      exact hqF _
  have h3 : (Matrix.of fun i => Θ (y i)) = Matrix.of y * Mᵀ := by
    ext i k
    rw [Matrix.of_apply, ← hM]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h3, Matrix.det_mul, Matrix.det_transpose, ← h1] at h2
  rw [← h2]
  field_simp

end GlobalTheory.DetInv.ScalarEx
