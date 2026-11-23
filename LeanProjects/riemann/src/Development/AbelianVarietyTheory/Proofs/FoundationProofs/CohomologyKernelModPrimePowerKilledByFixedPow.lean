import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsQuotientMapToGSProd

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.Kill

variable {l : ℕ} [Fact l.Prime]

theorem mem_of_memE (c : Coef l) {x : Qbar l} (hE : MemE c x) (hx : ‖x‖ ≤ 1) : x ∈ c.O := by
  obtain ⟨k, hk⟩ := hE
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hn : ‖(l : Qbar l) ^ k * x‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx
  obtain ⟨w, hw, e⟩ := Rec.exists_eq_pow_mul_of_norm_le hk hn
  have : x = w := mul_left_cancel₀ (pow_ne_zero k hl0) e
  rw [this]; exact hw

theorem adj_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    M.adjugate i j ∈ c.O := by
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [c.O.neg_mem, hM]

theorem norm_mulVec_le (c : Coef l) {A : Matrix (Fin 2) (Fin 2) (Qbar l)} (hA : ∀ i j, A i j ∈ c.O)
    {v : Fin 2 → Qbar l} (hv : ∀ j, ‖v j‖ ≤ 1) (i : Fin 2) : ‖(A *ᵥ v) i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
  · rw [norm_mul]; exact mul_le_one₀ (Rec.norm_le_one_of_mem (hA _ _)) (norm_nonneg _) (hv _)

end GlobalTheory.Ord2.Kill

namespace GlobalTheory.Ord2

open Kill in

theorem exists_pow_smul_cob1_of_cv_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l),
    (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → ∃ r : ℕ, ∀ (n : ℕ) (a : G ℚ Ω → Fin 2 → Qbar l)
      (y : Fin 2 → Qbar l), (∀ s i, a s i ∈ c.O) → VecE c y → (∀ s, Cv n (a s) (mat W s *ᵥ y - y)) →
      Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ r • a s) := by
  intro l _ Ω _ _ W c hW ⟨g, hg⟩
  set M := mat W g - 1 with hMdef
  have hMO : ∀ i j, M i j ∈ c.O := fun i j => by
    simp only [M, Matrix.sub_apply, Matrix.one_apply]
    split_ifs
    · exact c.O.sub_mem (hW g i j) c.O.one_mem
    · simpa using hW g i j
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hd : 0 < ‖M.det‖ := norm_pos_iff.2 hg
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hd hlinv
  refine ⟨r, fun n a y ha hy h => ?_⟩
  have hlr : ‖((l : ℕ) : Qbar l) ^ r‖ = (l : ℝ)⁻¹ ^ r := by rw [norm_pow, Rec.norm_natCast_l]
  have hlr1 : ‖((l : ℕ) : Qbar l) ^ r‖ ≤ 1 := by rw [hlr]; exact pow_le_one₀ hlpos.le hlinv.le
  have hln1 : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ 1 := by
    rw [norm_pow, Rec.norm_natCast_l]; exact pow_le_one₀ hlpos.le hlinv.le

  have hMy : ∀ j, ‖(M *ᵥ y) j‖ ≤ 1 := by
    intro j
    have e : (M *ᵥ y) j = a g j - (a g j - (mat W g *ᵥ y - y) j) := by
      simp [M, Matrix.sub_mulVec]
    rw [e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (Rec.norm_le_one_of_mem (ha g j)) ?_)
    rw [norm_neg]
    exact (h g j).trans hln1

  have hdy : ∀ i, ‖M.det * y i‖ ≤ 1 := by
    intro i
    have e : M.det * y i = (M.adjugate *ᵥ (M *ᵥ y)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      simp
    rw [e]
    exact norm_mulVec_le c (adj_mem c hMO) hMy i
  have hx : ∀ i, ((l : ℕ) : Qbar l) ^ r * y i ∈ c.O := by
    intro i
    apply mem_of_memE c
    · obtain ⟨k, hk⟩ := hy
      refine ⟨k, ?_⟩
      have e : (l : Qbar l) ^ k * (((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r * ((l : Qbar l) ^ k * y i) := by
        ring
      rw [e]
      exact c.O.mul_mem (natPow_mem c r) (hk i)
    · have h1 := hdy i
      rw [norm_mul] at h1 ⊢
      calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖y i‖ ≤ ‖M.det‖ * ‖y i‖ := by
            gcongr; rw [hlr]; exact hr.le
        _ ≤ 1 := h1
  refine ⟨fun i => ((l : ℕ) : Qbar l) ^ r * y i, hx, fun s _ i => ?_⟩
  have e : (((l : ℕ) : Qbar l) ^ r • a s) i - (mat W s *ᵥ (fun i => ((l : ℕ) : Qbar l) ^ r * y i) -
      fun i => ((l : ℕ) : Qbar l) ^ r * y i) i = ((l : ℕ) : Qbar l) ^ r * (a s i - (mat W s *ᵥ y - y) i) := by
    have : (fun i => ((l : ℕ) : Qbar l) ^ r * y i) = ((l : ℕ) : Qbar l) ^ r • y := by
      funext i; simp
    rw [this, Matrix.mulVec_smul]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold Cg
  rw [e, norm_mul]
  calc ‖((l : ℕ) : Qbar l) ^ r‖ * ‖a s i - (mat W s *ᵥ y - y) i‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hlr1 (h s i) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2
