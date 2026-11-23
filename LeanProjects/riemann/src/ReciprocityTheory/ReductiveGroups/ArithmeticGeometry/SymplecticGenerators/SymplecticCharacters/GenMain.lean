import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.GenFin

open Matrix

namespace ReciprocityTheory.ChartRestriction.G.Key.Chi

variable {g : ℕ}

theorem col_inr_step (k : Fin g) (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) (hF : ColsFixed k M)
    (hk : ∀ r, M r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) :
    ∃ O ∈ spH g, ColsFixed k O ∧
      (∀ r, O r (Sum.inl k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k)) ∧
      ∀ r, (O * M) r (Sum.inr k) = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inr k) := by
  have hrow : ∀ q, M (Sum.inr k) q = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr k) q :=
    row_inr_of_col_inl hM hk
  have hck : M (Sum.inr k) (Sum.inr k) = 1 := by rw [hrow]; simp
  have hlow : ∀ i : Fin g, (i : ℕ) < k → M (Sum.inr i) (Sum.inr k) = 0 := by
    intro i hi
    have hik : i ≠ k := by intro h; subst h; omega
    rw [row_inr_of_col_inl hM (hF i hi).1]; simp [Matrix.one_apply, hik]
  set c' : Fin g → ℤ := fun l => if (k : ℕ) < l then M (Sum.inr l) (Sum.inr k) else 0 with hc'
  have hdot : c' ⬝ᵥ Pi.single k 1 = 0 := by rw [dotProduct_single]; simp [hc']
  have hDmem : spDiag (rkU _ _ hdot) ∈ spH g := spDiag_mem _
  have hDF : ColsFixed k (spDiag (rkU _ _ hdot)) := by
    refine colsFixed_spDiag_rk hdot (fun i hi => ?_) (fun i hi => ?_)
    · have hik : i ≠ k := by intro h; subst h; omega
      simp [Pi.single_apply, hik]
    · simp only [hc']
      rw [if_neg (by omega)]
  have hDk : ∀ r, spDiag (rkU _ _ hdot) r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r
    rcases r with l | l
    · rw [spDiag, fromBlocks_apply₁₁, rkU_val]
      simp [vecMulVec_apply, hc', Matrix.one_apply]
    · simp [spDiag]
  set M1 := spDiag (rkU _ _ hdot) * M with hM1
  have hM1sp : M1 ∈ symplecticGroup (Fin g) ℤ :=
    (symplecticGroup (Fin g) ℤ).mul_mem (spH_le g hDmem) hM
  have hM1F : ColsFixed k M1 := colsFixed_mul hDF hF
  have hc1 : ∀ l, M1 (Sum.inr l) (Sum.inr k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (Sum.inr l) (Sum.inr k) := by
    intro l
    rw [hM1, spDiag_rk_mul_inr]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hck, mul_one, hc']
    rcases lt_trichotomy (l : ℕ) k with h | h | h
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_neg (by omega), hlow l h]; simp [Matrix.one_apply, hlk]
    · have e : l = k := Fin.ext h
      subst e; rw [if_neg (lt_irrefl _), hck]; simp
    · have hlk : l ≠ k := by intro e; subst e; omega
      rw [if_pos h]; simp [Matrix.one_apply, hlk]
  have ha1 : ∀ i : Fin g, (i : ℕ) < k → M1 (Sum.inl i) (Sum.inr k) = 0 := by
    intro i hi
    rw [row_inl_of_col_inr hM1sp (hM1F i hi).2]; simp [Matrix.one_apply]
  set S : Matrix (Fin g) (Fin g) ℤ := Matrix.of fun l m =>
    if m = k then (if l = k then -M1 (Sum.inl k) (Sum.inr k) else -M1 (Sum.inl l) (Sum.inr k))
    else (if l = k then -M1 (Sum.inl m) (Sum.inr k) else 0) with hS
  have hSsym : S.IsSymm := by
    refine Matrix.IsSymm.ext (fun l m => ?_)
    simp only [hS, of_apply]
    by_cases hl : l = k <;> by_cases hm : m = k <;> simp [hl, hm]
  have hSmem : spTransl S ∈ spH g := spTransl_mem hSsym
  have hSF : ColsFixed k (spTransl S) := by
    refine colsFixed_spTransl (fun i hi l => ?_)
    have hik : i ≠ k := by intro h; subst h; omega
    simp [hS, hik, ha1 i hi]
  have hSk : ∀ r, spTransl S r (Sum.inl k) =
      (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r (Sum.inl k) := by
    intro r; rcases r with l | l <;> simp [spTransl, Matrix.one_apply]
  refine ⟨spTransl S * spDiag (rkU _ _ hdot), (spH g).mul_mem hSmem hDmem, colsFixed_mul hSF hDF,
    fun r => by rw [mul_col_of_unit hDk]; exact hSk r, ?_⟩
  intro r
  rw [Matrix.mul_assoc]
  show (spTransl S * M1) r (Sum.inr k) = _
  rcases r with l | l
  · rw [spTransl_mul_inl]
    have hsum : ∑ m, S l m * M1 (Sum.inr m) (Sum.inr k) = S l k := by
      simp only [hc1, Matrix.one_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    simp only [hS, of_apply, if_true]
    by_cases hl : l = k
    · subst hl; simp
    · simp [hl]
  · rw [spTransl_mul_inr, hc1]

private theorem mem_symplecticGroup_of_mem_spH (g : ℕ) :
    ∀ O ∈ spH g, O ∈ symplecticGroup (Fin g) ℤ := by
  intro O hO
  have hle : Submonoid.closure (spGens g) ≤ symplecticGroup (Fin g) ℤ := by
    rw [Submonoid.closure_le]
    intro M hM'
    rw [SetLike.mem_coe]
    rcases hM' with ((⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ)
    · (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spTransl, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hS.eq]
    · have hU2 : (U : Matrix (Fin g) (Fin g) ℤ) * (↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ) = 1 := by
        first
        | exact Units.mul_inv U
        | exact Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U)
      have hU : ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ) * (U : Matrix (Fin g) (Fin g) ℤ)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hU2, Matrix.transpose_one]
      (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
      rw [spDiag, Matrix.J, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
      simp [hU, hU2]
      rw [← Matrix.transpose_mul]
      first
      | rw [Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U), Matrix.transpose_one]
      | rw [← Matrix.coe_units_inv, Units.mul_inv, Matrix.transpose_one]
    · rw [Set.mem_singleton_iff] at hJ
      rw [hJ]
      first
      | exact SymplecticGroup.J_mem
      | exact Matrix.J_mem
      | ((first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
         rw [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
           Matrix.fromBlocks_multiply]
         simp)

  exact hle hO

theorem exists_colsFixed (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)
    (hM : M ∈ symplecticGroup (Fin g) ℤ) : ∀ k : ℕ, k ≤ g → ∃ O ∈ spH g, ColsFixed k (O * M) := by
  have colmul : ∀ (A N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (c : Fin g ⊕ Fin g),
      (∀ r, N r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      (∀ r, A r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c) →
      ∀ r, (A * N) r c = (1 : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) r c := by
    intro A N c hN hA r
    rw [Matrix.mul_apply]
    simp_rw [hN]
    rw [← Matrix.mul_apply, Matrix.mul_one, hA]
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨1, one_mem _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨O1, hO1, hF1⟩ := ih (by omega)
    let kk : Fin g := ⟨k, by omega⟩
    have hS1 : O1 * M ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O1 hO1) hM
    obtain ⟨O2, hO2, hF2, h2⟩ := col_inl_step kk (O1 * M) hS1 hF1
    have hS2 : O2 * (O1 * M) ∈ symplecticGroup (Fin g) ℤ := mul_mem (mem_symplecticGroup_of_mem_spH g O2 hO2) hS1
    have hF2' : ColsFixed k (O2 * (O1 * M)) := fun i hi =>
      ⟨colmul _ _ _ (hF1 i hi).1 (hF2 i hi).1, colmul _ _ _ (hF1 i hi).2 (hF2 i hi).2⟩
    obtain ⟨O3, hO3, hF3, h3inl, h3⟩ := col_inr_step kk (O2 * (O1 * M)) hS2 hF2' h2
    refine ⟨O3 * (O2 * O1), mul_mem hO3 (mul_mem hO2 hO1), ?_⟩
    rw [show O3 * (O2 * O1) * M = O3 * (O2 * (O1 * M)) by simp only [Matrix.mul_assoc]]
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact ⟨colmul _ _ _ (hF2' i hi).1 (hF3 i hi).1, colmul _ _ _ (hF2' i hi).2 (hF3 i hi).2⟩
    · have hik : i = kk := Fin.ext hi
      rw [hik]
      exact ⟨colmul _ _ _ h2 h3inl, h3⟩

theorem spGen : SpGenStatement := by
  intro g M hM
  obtain ⟨A, rfl⟩ : ∃ A : symplecticGroup (Fin g) ℤ,
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = M := ⟨⟨M, hM⟩, rfl⟩
  obtain ⟨O, hO, hF⟩ := exists_colsFixed
    ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (A⁻¹).2 g le_rfl
  have h1 : O * ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 := by
    ext r c
    rcases c with i | i
    · exact (hF i i.isLt).1 r
    · exact (hF i i.isLt).2 r
  have h2 : ((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
      (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) = 1 :=
    congrArg Subtype.val (inv_mul_cancel A)
  have hOM : O = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
    calc O = O * (((A⁻¹ : symplecticGroup (Fin g) ℤ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) *
          (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ)) := by rw [h2, Matrix.mul_one]
      _ = (A : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [← hOM]
  exact hO

theorem closure_spGens_eq (g : ℕ) :
    Submonoid.closure (spGens g) = symplecticGroup (Fin g) ℤ := by
  refine le_antisymm ?_ (fun M hM => spGen g M hM)
  rw [Submonoid.closure_le]
  intro M hM'
  rw [SetLike.mem_coe]
  rcases hM' with ((⟨S, hS, rfl⟩ | ⟨U, rfl⟩) | hJ)
  · (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
    rw [spTransl, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hS.eq]
  · have hU2 : (U : Matrix (Fin g) (Fin g) ℤ) * (↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ) = 1 := by
      first
      | exact Units.mul_inv U
      | exact Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U)
    have hU : ((↑U⁻¹ : Matrix (Fin g) (Fin g) ℤ)ᵀ) * (U : Matrix (Fin g) (Fin g) ℤ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hU2, Matrix.transpose_one]
    (first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
    rw [spDiag, Matrix.J, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hU, hU2]
    rw [← Matrix.transpose_mul]
    first
    | rw [Matrix.mul_nonsing_inv _ (Matrix.isUnits_det_units U), Matrix.transpose_one]
    | rw [← Matrix.coe_units_inv, Units.mul_inv, Matrix.transpose_one]
  · rw [Set.mem_singleton_iff] at hJ
    rw [hJ]
    first
    | exact SymplecticGroup.J_mem
    | exact Matrix.J_mem
    | ((first | rw [SymplecticGroup.mem_iff] | rw [Matrix.mem_symplecticGroup_iff])
       rw [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
         Matrix.fromBlocks_multiply]
       simp)

end ReciprocityTheory.ChartRestriction.G.Key.Chi
