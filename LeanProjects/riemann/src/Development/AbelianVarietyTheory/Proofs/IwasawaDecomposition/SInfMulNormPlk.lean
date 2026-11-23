import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.GradedNorm

open Matrix

theorem det_mem {C : Type} [Field C] (W : ValuationSubring C) {k : ℕ} (A : Matrix (Fin k) (Fin k) C)
    (h : ∀ i j, A i j ∈ W) : A.det ∈ W := by
  rw [Matrix.det_apply']
  exact W.toSubring.sum_mem fun σ _ =>
    W.toSubring.mul_mem (intCast_mem W.toSubring _) (W.toSubring.prod_mem fun i _ => h _ _)

theorem plk_eq {C : Type} [Field C] {M n : ℕ} (c : Fin n → Fin (M + 1) → C)
    (u : Matrix (Fin (M + 1)) (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (hb : b.BlockTriangular id)
    (hc : (Matrix.of c)ᵀ = u * b) {k : ℕ} (hk : k ≤ n) (q : Fin (plN M k + 1)) :
    plk c (Fin.castLE hk) q =
      (u.submatrix (plE M k q) (Fin.castLE hk)).det * ∏ l : Fin k, b (Fin.castLE hk l) (Fin.castLE hk l) := by
  have h1 : (Matrix.of fun l l' => c (Fin.castLE hk l) (plE M k q l'))ᵀ =
      u.submatrix (plE M k q) (Fin.castLE hk) * b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext l' l
    have h2 := congrFun (congrFun hc (plE M k q l')) (Fin.castLE hk l)
    simp only [transpose_apply, of_apply] at h2 ⊢
    rw [h2, mul_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
    intro j hj
    have : b j (Fin.castLE hk l) = 0 := by
      apply hb
      by_contra hlt
      have hle : (j : ℕ) ≤ l := Fin.le_def.mp (not_lt.mp hlt)
      exact hj ⟨⟨j, lt_of_le_of_lt hle l.2⟩, rfl⟩
    rw [this, mul_zero]
  have h3 : (b.submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id := fun i j hij => hb hij
  unfold plk
  rw [← det_transpose, h1, det_mul, Matrix.det_of_isUpperTriangular h3]
  rfl

theorem norm_plk_max {C : Type} [NontriviallyNormedField C] (W : ValuationSubring C)
    (hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1) {M n : ℕ} (c : Fin n → Fin (M + 1) → C) (ι : Fin n → Fin (M + 1))
    (u : Matrix (Fin (M + 1)) (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (hb : b.BlockTriangular id)
    (hc : (Matrix.of c)ᵀ = u * b) {k : ℕ} (hk : k ≤ n) (q₀ : Fin (plN M k + 1))
    (hq : ∀ q, ‖plk c (Fin.castLE hk) q‖ ≤ ‖plk c (Fin.castLE hk) q₀‖) :
    ‖plk c (Fin.castLE hk) q₀‖ = ∏ l : Fin k, ‖b (Fin.castLE hk l) (Fin.castLE hk l)‖ := by
  apply le_antisymm
  · rw [plk_eq c u b hb hc hk, norm_mul, norm_prod]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      ((hW _).1 (det_mem W _ fun _ _ => huW _ _))
  · refine le_trans (le_of_eq ?_) (hq ((plE M k).symm (ι ∘ Fin.castLE hk)))
    rw [plk_eq c u b hb hc hk, Equiv.apply_symm_apply, norm_mul, norm_prod]
    have hMt : (u.submatrix (ι ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
      fun i j hij => hu0 _ _ hij
    rw [Matrix.det_of_isLowerTriangular _ hMt]
    simp [hu1]

theorem mem_of_mulVec {C : Type} [Field C] (W : ValuationSubring C) {m n : ℕ} (ι : Fin n → Fin m)
    (u : Matrix (Fin m) (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (y : Fin n → C)
    (hy : ∀ s, (u *ᵥ y) s ∈ W) (i : Fin n) : y i ∈ W := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have h1 : y i = (u *ᵥ y) (ι i) - ∑ j ∈ Finset.univ.erase i, u (ι i) j * y j := by
      rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hu1]
      ring
    rw [h1]
    refine W.toSubring.sub_mem (hy _) (W.toSubring.sum_mem fun j hj => ?_)
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact W.toSubring.mul_mem (huW _ _) (ih j h)
    · rw [hu0 _ _ h, zero_mul]
      exact W.toSubring.zero_mem

theorem sInf_mul_norm_plk : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (M n : ℕ) (c : Fin n → Fin (M + 1) → C) (i : Fin n) (q₀ : Fin (plN M i + 1)) (q₁ : Fin (plN M (i + 1) + 1)), plk c id ≠ 0 → (∀ q, ‖plk c (Fin.castLE i.2.le) q‖ ≤ ‖plk c (Fin.castLE i.2.le) q₀‖) → (∀ q, ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q‖ ≤ ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q₁‖) → sInf {r : ℝ | ∃ cf : Fin n → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∀ s, ‖(∑ j, cf j • c j) s‖ ≤ 1) ∧ r = ‖cf i‖⁻¹} * ‖plk c (Fin.castLE i.2.le) q₀‖ = ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q₁‖ := by
  intro C _ _ M n c i q₀ q₁ hne h₀ h₁
  let W : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  have hli : LinearIndependent C (Matrix.of c)ᵀᵀ := by
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
    have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (A := Matrix.of fun l l' => c l (plE M n q l')) hq
    exact LinearIndependent.of_comp (LinearMap.funLeft C C (plE M n q)) h2
  obtain ⟨ι, u, b, huW, hu0, hu1, hb, hbd, hc⟩ := GlobalTheory.exists_integral_pivot_decomposition C W _ _ _ hli
  have hsum : ∀ cf : Fin n → C, ∑ j, cf j • c j = u *ᵥ (b *ᵥ cf) := fun cf => by
    rw [mulVec_mulVec, ← hc]
    funext s
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hdiag : ∀ cf : Fin n → C, (∀ k, i < k → cf k = 0) → (b *ᵥ cf) i = b i i * cf i := fun cf hcf => by
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hb h, zero_mul]
    · rw [hcf j h, mul_zero]
  have hbdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd i).isUnit
  have hleast : IsLeast {r : ℝ | ∃ cf : Fin n → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧
      (∀ s, ‖(∑ j, cf j • c j) s‖ ≤ 1) ∧ r = ‖cf i‖⁻¹} ‖b i i‖ := by
    constructor
    · letI := b.invertibleOfIsUnitDet hbdet
      have hinv : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
      have hz : ∀ k, i < k → (b⁻¹ *ᵥ Pi.single i 1 : Fin n → C) k = 0 := fun k hk => by
        rw [mulVec_single_one]
        exact hinv hk
      have hbb : b *ᵥ (b⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, mul_nonsing_inv _ hbdet, one_mulVec]
      have h1 := hdiag _ hz
      rw [hbb, Pi.single_eq_same] at h1
      refine ⟨b⁻¹ *ᵥ Pi.single i 1, right_ne_zero_of_mul (h1 ▸ one_ne_zero), hz, fun s => ?_, ?_⟩
      · rw [hsum, hbb, mulVec_single_one]
        exact (hW _).1 (huW _ _)
      · rw [eq_inv_of_mul_eq_one_left h1.symm, norm_inv]
    · rintro r ⟨cf, hcf, hz, hint, rfl⟩
      have h1 := (hW _).1 (mem_of_mulVec W ι u huW hu0 hu1 (b *ᵥ cf)
        (fun s => (hW _).2 (hsum cf ▸ hint s)) i)
      rw [hdiag cf hz, norm_mul] at h1
      rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hcf)]
      exact h1
  rw [hleast.csInf_eq, norm_plk_max W hW c ι u b huW hu0 hu1 hb hc _ q₀ h₀,
    norm_plk_max W hW c ι u b huW hu0 hu1 hb hc _ q₁ h₁, Fin.prod_univ_castSucc, mul_comm]
  rfl

end GlobalTheory.FlagEmb.GradedNorm
