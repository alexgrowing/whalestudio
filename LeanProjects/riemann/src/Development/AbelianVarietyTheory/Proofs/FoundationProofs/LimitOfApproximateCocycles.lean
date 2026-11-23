import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallNormLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem qbarLVectorCongruent_integralMatrix_mulVec {l : ℕ} [Fact l.Prime] (c : Coef l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hM : ∀ i j, M i j ∈ c.O) {n : ℕ} {v w : Fin 2 → Qbar l} (h : Cv n v w) :
    Cv n (M *ᵥ v) (M *ᵥ w) := by
  intro i
  unfold Cg
  have e : (M *ᵥ v) i - (M *ᵥ w) i = M i 0 * (v 0 - w 0) + M i 1 * (v 1 - w 1) := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 0))).trans (h 0)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_mem_coef c (hM i 1))).trans (h 1)

theorem limit_cocycle_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  intro l _ Ω _ _ W c hW a z hco hloc hz
  rw [mem_Z1_iff_cocycle]
  refine ⟨?_, ?_⟩
  · refine continuous_pi fun i => ?_
    refine continuous_iff_continuousAt.2 fun s => ?_
    have key : Filter.Tendsto (fun t => z t i) (nhds s) (@nhds (Qbar l) UniformSpace.toTopologicalSpace (z s i)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨n, hn⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists
      filter_upwards [hloc n s] with t ht
      have h1 : Cg n (z t i) (z s i) :=
        cg_trans (hz n t i) (cg_trans (ht i) (cg_symm (hz n s i)))
      rw [dist_eq_norm]
      exact lt_of_le_of_lt h1 hn
    exact key
  · intro s t
    have hcol : ∀ v, (Loc.colRep W s) v = mat W s *ᵥ v := by
      intro v; simp [Loc.colRep, Matrix.toLin'_apply]
    rw [hcol]
    funext i
    refine eq_of_forall_cg fun n => ?_
    have hA : Cv n (z (s * t)) (a n (s * t)) := hz n (s * t)
    have hB := hco n s t
    have hC : Cv n (a n s + mat W s *ᵥ a n t) (z s + mat W s *ᵥ z t) := by
      intro j
      have h2 := qbarLVectorCongruent_integralMatrix_mulVec c (mat W s) (hW s) (cv_symm (hz n t)) j
      have h3 := cg_symm (hz n s j)
      unfold Cg at h2 h3 ⊢
      have e : (a n s + mat W s *ᵥ a n t) j - (z s + mat W s *ᵥ z t) j
          = (a n s j - z s j) + ((mat W s *ᵥ a n t) j - (mat W s *ᵥ z t) j) := by
        simp only [Pi.add_apply]; ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h2)
    exact (cv_trans hA (cv_trans hB hC)) i

end GlobalTheory.Ord2
