import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnimodularHermitianMatrixCongruentOneStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitaryTransitive

variable {E : Type} [NormedField E] [StarRing E]

theorem nsub [IsUltrametricDist E] (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)

def ext0 {r : ℕ} (x : Fin r → E) : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) x 0

@[simp] theorem snocZeroLastCoordinate_castSucc {r : ℕ} (x : Fin r → E) (j : Fin r) : ext0 x j.castSucc = x j := by
  simp [ext0]
@[simp] theorem snocZeroLastCoordinate_last {r : ℕ} (x : Fin r → E) : ext0 x (Fin.last r) = 0 := by
  simp [ext0]

theorem star_snocZeroLastCoordinate_dotProduct {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    star (ext0 x) ⬝ᵥ f = star x ⬝ᵥ (fun j => f j.castSucc) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

theorem dotProduct_snocZeroLastCoordinate {r : ℕ} (x : Fin r → E) (f : Fin (r + 1) → E) :
    f ⬝ᵥ ext0 x = (fun j => f j.castSucc) ⬝ᵥ x := by
  simp [dotProduct, Fin.sum_univ_castSucc]

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive
variable {E : Type} [Field E] [StarRing E]
theorem rank_one_entry {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (a b : Fin r → E) (m m' : Fin r) :
    (gᴴ * (replicateCol Unit a * replicateRow Unit b) * g) m m' = (gᴴ *ᵥ a) m * (b ᵥ* g) m' := by
  have e : gᴴ * (replicateCol Unit a * replicateRow Unit b) * g =
      replicateCol Unit (gᴴ *ᵥ a) * replicateRow Unit (b ᵥ* g) := by
    rw [Matrix.replicateCol_mulVec, Matrix.replicateRow_vecMul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e]; simp [Matrix.mul_apply]

theorem star_dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (w : Fin r → E) (m : Fin r) :
    star (star w ⬝ᵥ (fun j => g j m)) = (gᴴ *ᵥ w) m := by
  simp [dotProduct, Matrix.mulVec, star_sum, mul_comm]

theorem dot_col {r : ℕ} (g : Matrix (Fin r) (Fin r) E) (b : Fin r → E) (m : Fin r) :
    b ⬝ᵥ (fun j => g j m) = (b ᵥ* g) m := by
  simp [dotProduct, Matrix.vecMul]
end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive_of_last_unit (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E) (hv : ∀ i, ‖v i‖ ≤ 1) (h1 : star v ⬝ᵥ v = 1)
    (hn : ‖v (Fin.last r)‖ = 1) : ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  set w : Fin r → E := fun j => v j.castSucc with hw
  set G : Matrix (Fin r) (Fin r) E := 1 + replicateCol Unit (-w) * replicateRow Unit (star w) with hG
  have hGe : ∀ i j, G i j = (1 : Matrix (Fin r) (Fin r) E) i j - w i * star (w j) := by
    intro i j; simp [G, Matrix.mul_apply, sub_eq_add_neg]
  have hGh : G.IsHermitian := by
    apply Matrix.IsHermitian.ext; intro i j; rw [hGe, hGe]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [Matrix.one_apply, h, Ne.symm h, mul_comm]
  have hGi : ∀ i j, ‖G i j‖ ≤ 1 := by
    intro i j; rw [hGe]; refine (nsub _ _).trans (max_le ?_ ?_)
    · by_cases h : i = j <;> simp [Matrix.one_apply, h]
    · rw [norm_mul, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hv _)
  have hsplit : star v ⬝ᵥ v = star w ⬝ᵥ w + star (v (Fin.last r)) * v (Fin.last r) := by
    simp [dotProduct, Fin.sum_univ_castSucc, w]
  have hGd : ‖G.det‖ = 1 := by
    rw [hG, det_one_add_replicateCol_mul_replicateRow, dotProduct_neg]
    have : 1 + -(star w ⬝ᵥ w) = star (v (Fin.last r)) * v (Fin.last r) := by
      linear_combination h1.symm + hsplit
    rw [this, norm_mul, hst, hn]; norm_num
  obtain ⟨g, hgi, -, hg⟩ := GlobalTheory.T.unimodular_hermitian_matrix_congruent_one F E r G hGh hGi hGd
  set c : Fin r → E := fun m => star w ⬝ᵥ (fun j => g j m) with hc
  have hg' : ∀ m m', star (fun j => g j m) ⬝ᵥ (fun j => g j m') - star (c m) * c m' = (1 : Matrix (Fin r) (Fin r) E) m m' := by
    intro m m'
    have := congrFun (congrFun hg m) m'
    rw [← this, hG, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.add_apply, rank_one_entry,
      hc, star_dot_col, dot_col, Matrix.mulVec_neg]
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, sub_eq_add_neg]
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun i l =>
    Fin.lastCases (motive := fun _ => E) (v i) (fun m => ext0 (fun j => g j m) i - c m * v i) l
  have cl : (fun i => K i (Fin.last r)) = v := by funext i; simp [K]
  have cs : ∀ m, (fun i => K i m.castSucc) = ext0 (fun j => g j m) - c m • v := by
    intro m; funext i; simp [K]
  have key : ∀ a b, (star K * K) a b = star (fun i => K i a) ⬝ᵥ (fun i => K i b) := by
    intro a b; rfl
  have d2 : ∀ m, star v ⬝ᵥ ext0 (fun j => g j m) = c m := by
    intro m; rw [dotProduct_snocZeroLastCoordinate]; rfl
  have d3 : ∀ m, star (ext0 (fun j => g j m)) ⬝ᵥ v = star (c m) := by
    intro m; rw [star_snocZeroLastCoordinate_dotProduct, hc, star_dot_col]; rfl
  have d4 : ∀ m m', star (ext0 (fun j => g j m)) ⬝ᵥ ext0 (fun j => g j m') =
      star (fun j => g j m) ⬝ᵥ (fun j => g j m') := by
    intro m m'; rw [star_snocZeroLastCoordinate_dotProduct]; simp
  have hU : star K * K = 1 := by
    ext a b
    rw [key]
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rw [cl, h1]; simp
      | cast m' =>
        rw [cl, cs, dotProduct_sub, dotProduct_smul, d2, h1, smul_eq_mul, mul_one, sub_self,
          Matrix.one_apply_ne (Fin.castSucc_ne_last m').symm]
    | cast m =>
      induction b using Fin.lastCases with
      | last =>
        rw [cl, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, d3, h1]
        simp [Matrix.one_apply, (Fin.castSucc_ne_last m)]
      | cast m' =>
        rw [cs, cs, star_sub, star_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub, dotProduct_sub,
          dotProduct_smul, dotProduct_smul, d2, d3, d4, h1]
        have e1 : (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) m.castSucc m'.castSucc =
            (1 : Matrix (Fin r) (Fin r) E) m m' := by
          simp [Matrix.one_apply, Fin.castSucc_inj]
        rw [e1, ← hg' m m']
        simp only [smul_eq_mul]
        ring
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, ?_, ?_⟩
  · intro i l
    show ‖K i l‖ ≤ 1
    induction l using Fin.lastCases with
    | last => simpa [K] using hv i
    | cast m =>
      simp only [K, Matrix.of_apply, Fin.lastCases_castSucc]
      have hcm : ‖c m‖ ≤ 1 := by
        rw [hc]
        exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun j _ => by
          rw [norm_mul, Pi.star_apply, hst]; exact mul_le_one₀ (hv _) (norm_nonneg _) (hgi _ _))
      refine (nsub _ _).trans (max_le ?_ ?_)
      · induction i using Fin.lastCases with
        | last => simp
        | cast j => simpa using hgi j m
      · rw [norm_mul]; exact mul_le_one₀ hcm (norm_nonneg _) (hv _)
  · show K *ᵥ Pi.single (Fin.last r) 1 = v
    rw [Matrix.mulVec_single_one]; exact cl

end GlobalTheory.UnitaryTransitive

namespace GlobalTheory.UnitaryTransitive

theorem uO_transitive : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (v : Fin (r + 1) → E), (∀ i, ‖v i‖ ≤ 1) → star v ⬝ᵥ v = 1 →
    ∃ k ∈ uO (r + 1) E, k.1 *ᵥ Pi.single (Fin.last r) 1 = v := by
  intro F E _ _ _ _ _ r v hv h1
  haveI := Unram.ultraE (F := F) (E := E)
  have hst : ∀ x : E, ‖star x‖ = ‖x‖ := Unram.norm_star (F := F)
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le (Finset.univ : Finset (Fin (r + 1)))
    (fun i => star (v i) * v i)
  have hs : (∑ j, star (v j) * v j) = 1 := h1
  rw [hs, norm_one, norm_mul, hst] at hi
  have hvi : ‖v i‖ = 1 := by nlinarith [hv i, norm_nonneg (v i)]
  set σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap i (Fin.last r) with hσ
  have hσσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ _
  have h1' : star (v ∘ σ) ⬝ᵥ (v ∘ σ) = 1 := by
    rw [← hs]; exact Equiv.sum_comp σ (fun j => star (v j) * v j)
  have hn' : ‖(v ∘ σ) (Fin.last r)‖ = 1 := by simp [hσ, hvi]
  obtain ⟨k, hk, hkv⟩ := uO_transitive_of_last_unit F E r (v ∘ σ) (fun j => hv _) h1' hn'
  let K : Matrix (Fin (r + 1)) (Fin (r + 1)) E := k.1.submatrix σ id
  have hU : star K * K = 1 := by
    have hk1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
    ext a b
    rw [← hk1]
    simp only [K, Matrix.mul_apply, Matrix.star_apply, Matrix.submatrix_apply, id]
    exact Equiv.sum_comp σ (fun j => star (k.1 j a) * k.1 j b)
  refine ⟨⟨K, Matrix.mem_unitaryGroup_iff'.2 hU⟩, fun a b => hk (σ a) b, ?_⟩
  show K *ᵥ Pi.single (Fin.last r) 1 = v
  funext j
  have := congrFun hkv (σ j)
  rw [Matrix.mulVec_single_one] at this ⊢
  simpa [K, hσσ] using this

end GlobalTheory.UnitaryTransitive
