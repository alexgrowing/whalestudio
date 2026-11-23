import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.DetLowUni

noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

theorem eventually_not_mem_of_finite {F : Set ℂ} (hF : F.Finite) : ∀ᶠ x in 𝓝[≠] (0 : ℂ), x ∉ F := by
  have h1 : ∀ᶠ x in 𝓝 (0 : ℂ), x ∉ F \ {0} :=
    (hF.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with x hx hx0
  exact fun hxF => hx ⟨hxF, hx0⟩

theorem det_add_smul_eventually {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (A + x • (1 : Matrix (Fin k) (Fin k) ℂ)).det ≠ 0 := by
  have hp : (-A).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  filter_upwards [eventually_not_mem_of_finite (Polynomial.finite_setOf_isRoot hp)] with x hx
  intro h0
  apply hx
  show Polynomial.IsRoot _ x
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply, sub_neg_eq_add, add_comm,
    ← Matrix.smul_one_eq_diagonal]
  exact h0

theorem dense_LU {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℂ), (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).det ≠ 0 ∧
      ∃ L U : Matrix (Fin n) (Fin n) ℂ, LowUni L ∧ UpTri U ∧ g + x • (1 : Matrix (Fin n) (Fin n) ℂ) = L * U := by
  have hsub : ∀ (x : ℂ) (m : ℕ) (hm : m ≤ n),
      (g + x • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hm) (Fin.castLE hm) =
        g.submatrix (Fin.castLE hm) (Fin.castLE hm) + x • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro x m hm
    simp only [Matrix.submatrix_add, Matrix.submatrix_smul, Pi.add_apply, Pi.smul_apply]
    rw [Matrix.submatrix_one _ (Fin.castLE_injective hm)]
  have hmin : ∀ᶠ x in 𝓝[≠] (0 : ℂ), ∀ m : Fin (n + 1),
      (g.submatrix (Fin.castLE (Nat.lt_succ_iff.mp m.2)) (Fin.castLE (Nat.lt_succ_iff.mp m.2)) +
        x • (1 : Matrix (Fin m) (Fin m) ℂ)).det ≠ 0 :=
    Filter.eventually_all.2 fun m => det_add_smul_eventually _
  filter_upwards [det_add_smul_eventually g, hmin] with x hdet hm
  refine ⟨hdet, PI.UnitaryGroupMassFormula.HwConjInf.exists_LU n _ (fun k hk => ?_)⟩
  rw [hsub]
  exact hm ⟨_, by omega⟩

theorem tendsto_add_smul {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝[≠] 0) (𝓝 g) := by
  have h : Tendsto (fun x : ℂ => g + x • (1 : Matrix (Fin n) (Fin n) ℂ)) (𝓝 0)
      (𝓝 (g + (0 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) :=
    tendsto_const_nhds.add (tendsto_id.smul_const _)
  rw [zero_smul, add_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

end PI.UnitaryGroupMassFormula.HwConjInf
