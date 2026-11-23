import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem rankOne {F : Type} [Field F] (b d : Fin 2 → F) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : d 0 * b 0 + d 1 * b 1 = 0) :
    ∃ m : GL (Fin 2) F, Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
  have key : ∀ u0 u1 : F, u0 * b 0 + u1 * b 1 = 1 → ∃ m : GL (Fin 2) F,
      Matrix.vecMulVec b d = (m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val := by
    intro u0 u1 hu
    have hdet : (!![u0, u1; d 0, d 1] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
      rw [Matrix.det_fin_two_of]
      intro h0
      apply hd
      funext i
      fin_cases i
      · show d 0 = 0
        linear_combination (-d 0) * hu + u0 * h - b 1 * h0
      · show d 1 = 0
        linear_combination (-d 1) * hu + u1 * h + b 0 * h0
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, ?_⟩
    rw [Matrix.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply, Matrix.single_apply]
    · linear_combination d 0 * hu
    · linear_combination d 1 * hu
    · linear_combination d 0 * h
    · linear_combination d 1 * h
  by_cases h0 : b 0 = 0
  · have h1 : b 1 ≠ 0 := fun h1 => hb (by funext i; fin_cases i <;> simpa)
    exact key 0 (b 1)⁻¹ (by simp [h1])
  · exact key (b 0)⁻¹ 0 (by simp [h0])

private theorem core {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ) (p q : Fin (2 + 2) → F)
    (hp : ∀ i : Fin (2 + 2), r ≤ (i : ℕ) → (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p i = 0)
    (hq : ∀ j : Fin (2 + 2), (j : ℕ) < r → Matrix.vecMul q γ.val j = 0)
    (h : ((fun i => q (Fin.castAdd 2 i)) = 0 ∧ (fun i => q (Fin.natAdd 2 i)) ≠ 0 ∧ (fun i => p (Fin.natAdd 2 i)) ≠ 0) ∨
      ((fun i => p (Fin.natAdd 2 i)) = 0 ∧ (fun i => p (Fin.castAdd 2 i)) ≠ 0 ∧ (fun i => q (Fin.castAdd 2 i)) ≠ 0)) :
    ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  set l := (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec p with hl
  set v := Matrix.vecMul q γ.val with hv
  have hX : blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) = Matrix.vecMulVec l v := by
    ext i j
    rw [blockEntry_apply, Matrix.vecMulVec_apply]
    split_ifs with hij
    · rfl
    · by_cases hi : (i : ℕ) < r
      · rw [hq j (by omega), mul_zero]
      · rw [hp i (by omega), zero_mul]
  have hE : (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry (fun s : UPos (2 + 2) r => l s.1.1 * v s.1.2) *
      (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.vecMulVec p q := by
    rw [hX, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hl, hv, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul,
      Units.mul_inv, Matrix.one_mulVec, Matrix.vecMul_one]
  have hdot : q ⬝ᵥ p = 0 := by
    have h1 : v ⬝ᵥ l = q ⬝ᵥ p := by
      rw [hl, hv, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · rw [hq i hi, zero_mul]
    · rw [hp i (by omega), mul_zero]
  rw [dotProduct, Fin.sum_univ_add, Fin.sum_univ_two, Fin.sum_univ_two] at hdot
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have h1' : ∀ i, q (Fin.castAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h3 h2 (by simpa only [h1', zero_mul, zero_add] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inl (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', mul_zero,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]
  · have h1' : ∀ i, p (Fin.natAdd 2 i) = 0 := congrFun h1
    obtain ⟨m, hm⟩ := rankOne _ _ h2 h3 (by simpa only [h1', mul_zero, add_zero] using hdot)
    refine ⟨_, m, Matrix.vecMulVec (fun i => p (Fin.castAdd 2 i)) (fun i => q (Fin.natAdd 2 i)), Or.inr (hE.trans ?_)⟩
    rw [← hm]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.vecMulVec_apply, h1', zero_mul,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply]

private theorem perp {F : Type} [Field F] (a : Fin 2 → F) (ha : a ≠ 0) :
    ∃ c : Fin 2 → F, c ≠ 0 ∧ ∑ i, c i * a i = 0 := by
  refine ⟨![a 1, -a 0], fun h => ha ?_, ?_⟩
  · have h0 := congrFun h 0
    have h1 := congrFun h 1
    funext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  · simp [Fin.sum_univ_two]
    ring

private theorem halves {F : Type} [Field F] (p : Fin (2 + 2) → F) (h1 : (fun i => p (Fin.castAdd 2 i)) = 0)
    (h2 : (fun i => p (Fin.natAdd 2 i)) = 0) : p = 0 := by
  funext i
  exact Fin.addCases (fun i => congrFun h1 i) (fun i => congrFun h2 i) i

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.linAlg :
    ∀ {F : Type} [Field F] (γ : GL (Fin (2 + 2)) F) (r : ℕ), (r = 1 ∨ r = 3 ∨ (r = 2 ∧
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2) ≠ 0 ∧ ((γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det = 0)) →
      ∃ (X₀ : UPos (2 + 2) r → F) (m : GL (Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F),
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 C 0 ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val)) ∨
        (γ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) * blockEntry X₀ * (γ⁻¹ : GL (Fin (2 + 2)) F).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks ((m⁻¹ : GL (Fin 2) F).val * Matrix.single 0 1 1 * m.val) C 0 0) := by
  intro F _ γ r hr
  have hcol : ∀ k i : Fin (2 + 2), (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s k) i =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) i k := fun k i => by
    rw [← Units.inv_mul γ]; rfl
  have hrow : ∀ k j : Fin (2 + 2), Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val k s) γ.val j =
      (1 : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F) k j := fun k j => by
    rw [← Units.inv_mul γ]; rfl
  rcases hr with rfl | rfl | ⟨rfl, hne, hdet⟩
  · have hp : ∀ i : Fin (2 + 2), 1 ≤ (i : ℕ) →
        (γ⁻¹ : GL (Fin (2 + 2)) F).val.mulVec (fun s => γ.val s 0) i = 0 := fun i hi => by
      rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      simp at hi
    have h0 : ∀ j : Fin (2 + 2), (j : ℕ) < 1 → j = 0 := fun j hj => Fin.ext (by simpa using hj)
    by_cases hb : (fun i => γ.val (Fin.natAdd 2 i) 0) = 0
    · have ha : (fun i => γ.val (Fin.castAdd 2 i) 0) ≠ 0 := fun ha => by
        have := hcol 0 0
        rw [halves (fun s => γ.val s 0) ha hb] at this
        simp at this
      obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 1 _ (Fin.append c 0) hp (fun j hj => ?_) (Or.inr ⟨hb, ha, by simpa only [Fin.append_left] using hc⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 1 _ (Fin.append 0 c) hp (fun j hj => ?_)
        (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hb⟩)
      rw [h0 j hj, Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add] using hs
  · have hq : ∀ j : Fin (2 + 2), (j : ℕ) < 3 →
        Matrix.vecMul (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) γ.val j = 0 := fun j hj => by
      rw [hrow, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hj
    have h0 : ∀ j : Fin (2 + 2), 3 ≤ (j : ℕ) → j = 3 := fun j hj => Fin.ext (by
      have := j.2
      show (j : ℕ) = 3
      omega)
    by_cases ha : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.castAdd 2 i)) = 0
    · have hb : (fun i => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 (Fin.natAdd 2 i)) ≠ 0 := fun hb => by
        have := hrow 3 3
        rw [halves (fun s => (γ⁻¹ : GL (Fin (2 + 2)) F).val 3 s) ha hb, Matrix.zero_vecMul, Matrix.one_apply_eq] at this
        exact zero_ne_one this
      obtain ⟨c, hc, hs⟩ := perp _ hb
      refine core γ 3 (Fin.append 0 c) _ (fun j hj => ?_) hq (Or.inl ⟨ha, hb, by simpa only [Fin.append_right] using hc⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
        mul_comm] using hs
    · obtain ⟨c, hc, hs⟩ := perp _ ha
      refine core γ 3 (Fin.append c 0) _ (fun j hj => ?_) hq
        (Or.inr ⟨by funext i; simp only [Fin.append_right], by simpa only [Fin.append_left] using hc, ha⟩)
      rw [h0 j hj, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
      simpa only [Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        mul_comm] using hs
  · obtain ⟨c, hc, hs⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, (fun i => γ.val (Fin.natAdd 2 i) (Fin.castAdd 2 k)) ≠ 0 := by
      by_contra hall
      apply hne
      ext i k
      by_contra hik
      exact hall ⟨k, fun h => hik (congrFun h i)⟩
    refine core γ 2 (fun s => γ.val s (Fin.castAdd 2 k)) (Fin.append 0 c) (fun i hi => ?_) (fun j hj => ?_)
      (Or.inl ⟨by funext i; simp only [Fin.append_left], by simpa only [Fin.append_right] using hc, hk⟩)
    · rw [hcol, Matrix.one_apply_ne]
      rintro rfl
      have := k.2
      simp only [Fin.val_castAdd] at hi
      omega
    · have hj' : j = Fin.castAdd 2 ⟨j, hj⟩ := rfl
      rw [hj', Matrix.vecMul, dotProduct, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      exact congrFun hs ⟨j, hj⟩
