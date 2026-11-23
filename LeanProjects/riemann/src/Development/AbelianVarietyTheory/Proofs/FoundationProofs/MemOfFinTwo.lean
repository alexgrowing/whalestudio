import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems

namespace GlobalTheory.FinTwoMembership

open Matrix

theorem mem_of_fin_two {R : Type*} [CommRing R] (S : Subring R) (M : Matrix (Fin 2) (Fin 2) R)
    (y z : Fin 2 → R) (u : R) (hM : ∀ i j, M i j ∈ S) (hy : ∀ i, y i ∈ S) (hz : ∀ i, z i ∈ S)
    (hu : u ∈ S) :
    M.det * u - ((M.adjugate *ᵥ y) 0 * z 1 - (M.adjugate *ᵥ y) 1 * z 0) ∈ S := by
  have hadj : ∀ i j, M.adjugate i j ∈ S := by
    intro i j
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [S.neg_mem, hM]
  have hv : ∀ i, (M.adjugate *ᵥ y) i ∈ S := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    exact S.add_mem (S.mul_mem (hadj _ _) (hy _)) (S.mul_mem (hadj _ _) (hy _))
  have hdet : M.det ∈ S := by
    rw [Matrix.det_fin_two]
    exact S.sub_mem (S.mul_mem (hM _ _) (hM _ _)) (S.mul_mem (hM _ _) (hM _ _))
  exact S.sub_mem (S.mul_mem hdet hu)
    (S.sub_mem (S.mul_mem (hv _) (hz _)) (S.mul_mem (hv _) (hz _)))

theorem ht_mem : ∀ {Ω : Type} [inst : Field Ω] [inst_1 : Algebra ℚ Ω] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
    (c : UpperTheory.V.HV.Coef l) (W : GlobalTheory.Ord2.R2 Ω l) (y z : Formalism.ConjugateSelfDual.G ℚ Ω → Fin (2 : ℕ) → Formalism.ConjugateSelfDual.Qbar l)
    (u : Formalism.ConjugateSelfDual.G ℚ Ω → Formalism.ConjugateSelfDual.Qbar l),
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i j : Fin (2 : ℕ)), GlobalTheory.Ord2.mat W s i j ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), y s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω) (i : Fin (2 : ℕ)), z s i ∈ UpperTheory.V.HV.Coef.O c) →
    (∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), u s ∈ UpperTheory.V.HV.Coef.O c) →
    ∀ (s : Formalism.ConjugateSelfDual.G ℚ Ω), GlobalTheory.Ord2.ht W y z u s ∈ UpperTheory.V.HV.Coef.O c := by
  intro Ω _ _ l _ c W y z u hW hy hz hu s
  have hM : ∀ i j, (GlobalTheory.Ord2.mat W s - 1) i j ∈ c.O.toSubring := by
    intro i j
    rw [Matrix.sub_apply]
    refine c.O.toSubring.sub_mem (hW s i j) ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact c.O.toSubring.one_mem
    · exact c.O.toSubring.zero_mem
  exact mem_of_fin_two c.O.toSubring _ (y s) (z s) (u s) hM (hy s) (hz s) (hu s)

end GlobalTheory.FinTwoMembership
