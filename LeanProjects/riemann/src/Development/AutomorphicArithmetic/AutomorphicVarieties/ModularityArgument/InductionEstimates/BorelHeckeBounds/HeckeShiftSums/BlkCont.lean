import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.VolOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.ReductionSiegel

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R]

private theorem vl (i : Fin 2) : ((finSumFinEquiv (Sum.inl i) : Fin (2 + 2)) : ℕ) = i := rfl

private theorem vr (i : Fin 2) : ((finSumFinEquiv (Sum.inr i) : Fin (2 + 2)) : ℕ) = 2 + i := rfl

private theorem blk_val' (x y : GL (Fin 2) R) :
    (blk x y).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks x.val 0 0 y.val) := rfl

private theorem blk_low (x y : GL (Fin 2) R) (i j : Fin (2 + 2)) (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    (blk x y).val i j = 0 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [vl] at hi; omega
  · rfl
  · rfl
  · rw [vr] at hj; omega

private theorem blk_tri (x y : GL (Fin 2) R) (hx : x.val.IsUpperTriangular) (hy : y.val.IsUpperTriangular) :
    (blk x y).val.IsUpperTriangular := by
  intro i j hij
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · have h : ((finSumFinEquiv (Sum.inl j) : Fin (2 + 2)) : ℕ) < (finSumFinEquiv (Sum.inl i) : Fin (2 + 2)) := hij
    rw [vl, vl] at h
    exact hx h
  · rfl
  · rfl
  · have h : ((finSumFinEquiv (Sum.inr j) : Fin (2 + 2)) : ℕ) < (finSumFinEquiv (Sum.inr i) : Fin (2 + 2)) := hij
    rw [vr, vr] at h
    exact hy (show (j : ℕ) < i by omega)

private theorem unip_tri (X : UPos (2 + 2) 2 → R) : (unipGL X).val.IsUpperTriangular := by
  intro i j hij
  have h : (j : ℕ) < i := hij
  have hne : i ≠ j := fun e => by subst e; omega
  simp only [coe_unipGL, unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply_ne hne, zero_add]
  rw [dif_neg (by omega)]

private theorem sandwich {A B : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R}
    (hA : ∀ i a : Fin (2 + 2), 2 ≤ (i : ℕ) → (a : ℕ) < 2 → A i a = 0)
    (hB : ∀ i a : Fin (2 + 2), 2 ≤ (i : ℕ) → (a : ℕ) < 2 → B i a = 0) (Z : UPos (2 + 2) 2 → R) :
    ∃ Y : UPos (2 + 2) 2 → R, A * blockEntry Z * B = blockEntry Y := by
  refine ⟨fun p => (A * blockEntry Z * B) p.1.1 p.1.2, ?_⟩
  ext i j
  rw [blockEntry_apply]
  split_ifs with h
  · rfl
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun a _ => ?_
    rw [blockEntry_apply]
    split_ifs with h'
    · by_cases hi : 2 ≤ (i : ℕ)
      · rw [hA i a hi h'.1, zero_mul, zero_mul]
      · rw [hB b j h'.2 (by omega), mul_zero]
    · rw [mul_zero, zero_mul]

private theorem blk_unip (x y : GL (Fin 2) R) (X : UPos (2 + 2) 2 → R) :
    ∃ Y : UPos (2 + 2) 2 → R, blk x y * unipGL X = unipGL Y * blk x y := by
  obtain ⟨Y, hY⟩ := sandwich (blk_low x y) (blk_low x⁻¹ y⁻¹) X
  refine ⟨Y, ?_⟩
  rw [← mul_inv_eq_iff_eq_mul]
  apply Units.ext
  have e : (blk x y)⁻¹ = blk x⁻¹ y⁻¹ := Units.ext rfl
  simp only [Units.val_mul, coe_unipGL, unipMatrix]
  rw [← hY, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, e]

private theorem blk_cont' [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun p : GL (Fin 2) R × GL (Fin 2) R => blk p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Continuous.matrix_fromBlocks (Units.continuous_val.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_val.comp continuous_snd)).matrix_reindex _ _
  · exact (Continuous.matrix_fromBlocks (Units.continuous_coe_inv.comp continuous_fst) continuous_const continuous_const
      (Units.continuous_coe_inv.comp continuous_snd)).matrix_reindex _ _

private theorem blk_diag (d : Fin (2 + 2) → Rˣ) :
    diagUnits (2 + 2) d = blk (diagUnits 2 fun i => d (Fin.castAdd 2 i)) (diagUnits 2 fun i => d (Fin.natAdd 2 i)) := by
  apply Units.ext
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk_val', Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, coe_diagUnits,
    Matrix.fromBlocks_diagonal, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> rfl

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.redEx :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Red ω t := by
  intro K _ _
  obtain ⟨ω₄, hc₄, hb₄, t₄, ht₄, h₄⟩ := exists_siegelSet (K := K) (2 + 2)
  obtain ⟨ω₂, hc₂, hb₂, t₂, ht₂, h₂⟩ := exists_siegelSet (K := K) 2
  obtain ⟨-, -, C, hC, -, hCX⟩ := volOne (K := K) (2 + 2) 2
  obtain ⟨hlv, -, -, -, -, hmul, -, -, -, -, hK, hmax⟩ := blkLaws (K := K)
  have hz : zt K 0 = 1 := by
    rw [zt, ← map_one (centralSection K 2)]
    exact congrArg _ (Subtype.ext Real.exp_zero)
  have hlv0 : ∀ a b : G1 K 2, ((lv a b 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
      blk (a : AdelicGLn.AdelicGL K 2) (b : AdelicGLn.AdelicGL K 2) := fun a b => by
    rw [hlv, neg_zero, hz, mul_one, mul_one]
  let F : (UPos (2 + 2) 2 → 𝔸[K]) × AdelicGLn.AdelicGL K 2 × AdelicGLn.AdelicGL K 2 → AdelicGLn.AdelicGL K (2 + 2) :=
    fun p => unipGL p.1 * blk p.2.1 p.2.2
  have hF : Continuous F := (continuous_unipGL.comp continuous_fst).mul (blk_cont'.comp continuous_snd)
  refine ⟨ω₄ ∪ F '' (C ×ˢ ω₂ ×ˢ ω₂), min t₄ t₂, ⟨hc₄.union ((hC.prod (hc₂.prod hc₂)).image hF), ?_⟩,
    lt_min ht₄ ht₂, fun x => ?_, fun z => ?_⟩
  · rintro _ (h | ⟨p, ⟨-, h1, h2⟩, rfl⟩)
    · exact hb₄ h
    · exact Subgroup.mul_mem _ (mem_adelicBorel.2 (unip_tri p.1))
        (mem_adelicBorel.2 (blk_tri _ _ (mem_adelicBorel.1 (hb₂ h1)) (mem_adelicBorel.1 (hb₂ h2))))
  · obtain ⟨γ, b, hb, _, ⟨r, hr, hrt, rfl⟩, k, hk, e⟩ := h₄ x
    refine ⟨⟨AdelicGLn.diagonal K _ γ, rationalGL_le_normOneGL ⟨γ, rfl⟩⟩, ⟨γ, rfl⟩, r,
      ⟨hr, b, Or.inl hb, k, hk, e⟩, fun i j hij => ?_⟩
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (hr j).le).trans (hrt i j hij)
  · obtain ⟨X, m₁, m₂, s, k, hk, rfl⟩ := iwa z
    obtain ⟨γ₁, b₁, hb₁, _, ⟨r₁, hr₁, hrt₁, rfl⟩, k₁, hk₁, e₁⟩ := h₂ ((m₁ : AdelicGLn.AdelicGL K 2) * zt K s)
    obtain ⟨γ₂, b₂, hb₂', _, ⟨r₂, hr₂, hrt₂, rfl⟩, k₂, hk₂, e₂⟩ := h₂ ((m₂ : AdelicGLn.AdelicGL K 2) * zt K (-s))
    let g₁ : Gam K 2 := ⟨⟨AdelicGLn.diagonal K _ γ₁, rationalGL_le_normOneGL ⟨γ₁, rfl⟩⟩, ⟨γ₁, rfl⟩⟩
    let g₂ : Gam K 2 := ⟨⟨AdelicGLn.diagonal K _ γ₂, rationalGL_le_normOneGL ⟨γ₂, rfl⟩⟩, ⟨γ₂, rfl⟩⟩
    obtain ⟨Y, hY⟩ := blk_unip (AdelicGLn.diagonal K _ γ₁) (AdelicGLn.diagonal K _ γ₂) X
    obtain ⟨ξ, hξ⟩ := hCX Y
    have hρ : ∀ i : Fin (2 + 2), 0 < (Fin.append r₁ r₂ : Fin (2 + 2) → ℝ) i := fun i => by
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · rw [Fin.append_left]; exact hr₁ i
      · rw [Fin.append_right]; exact hr₂ i
    have hkk : blk k₁ k₂ ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := by
      have := hK ⟨k₁, (hmax 2).2 k₁ hk₁⟩ hk₁ ⟨k₂, (hmax 2).2 k₂ hk₂⟩ hk₂
      rw [← hlv0 ⟨k₁, (hmax 2).2 k₁ hk₁⟩ ⟨k₂, (hmax 2).2 k₂ hk₂⟩]
      exact this
    have hk' : (k : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))) := hk
    have hmem : F (ξ.1 + Y, b₁, b₂) ∈ ω₄ ∪ F '' (C ×ˢ ω₂ ×ˢ ω₂) :=
      Or.inr (Set.mem_image_of_mem F ⟨hξ, hb₁, hb₂'⟩)
    have hδ : nn ξ.1 * lv (g₁ : G1 K 2) (g₂ : G1 K 2) 0 ∈ PK K := ((pkLaws (K := K)).2.1 _).2 ⟨ξ, g₁, g₂, rfl⟩
    refine ⟨nn ξ.1 * lv (g₁ : G1 K 2) (g₂ : G1 K 2) 0, hδ, Fin.append r₁ r₂,
      ⟨hρ, F (ξ.1 + Y, b₁, b₂), hmem, blk k₁ k₂ * (k : AdelicGLn.AdelicGL K (2 + 2)),
        Subgroup.mul_mem _ hkk hk', ?_⟩, ?_, ?_⟩
    · rw [blk_diag]
      simp only [Fin.append_left, Fin.append_right, F, Subgroup.coe_mul, hlv0, coe_unipOne, unipGL_add]
      rw [hlv]
      change unipGL ξ.1 * blk (AdelicGLn.diagonal K _ γ₁) (AdelicGLn.diagonal K _ γ₂) * _ = _
      simp only [← mul_assoc]
      rw [mul_assoc (unipGL ξ.1) _ (unipGL X), hY, ← mul_assoc, mul_assoc (unipGL ξ.1 * unipGL Y), hmul,
        mul_assoc (unipGL ξ.1 * unipGL Y) (blk b₁ b₂), hmul, mul_assoc (unipGL ξ.1 * unipGL Y) (blk (b₁ * _) (b₂ * _)), hmul,
        ← e₁, ← e₂]
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hr₁ 1).le).trans (hrt₁ 0 1 rfl)
    · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (hr₂ 1).le).trans (hrt₂ 0 1 rfl)
