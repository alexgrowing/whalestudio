import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ParHaar

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem unip_blocks' {a b : ℕ} {R : Type} [CommRing R] (X : UPos (a + b) a → R) :
    ∃ B, (unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks 1 B 0 (1 : Matrix (Fin b) (Fin b) R) := by
  refine ⟨((unipMatrix X).submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂, ?_⟩
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Matrix.toBlocks₁₂, Fin.ext_iff] <;> omega

private theorem unip_blk' {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) :
    ∃ B, (unipGL X * blk a b).val.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks a.val B 0 b.val := by
  obtain ⟨B, hB⟩ := unip_blocks' X
  refine ⟨B * b.val, ?_⟩
  rw [Units.val_mul, ← Matrix.submatrix_mul_equiv _ _ _ finSumFinEquiv, coe_unipGL, hB]
  simp [blk, Matrix.fromBlocks_multiply]

private theorem ret_zt {K : Type} [Field K] [NumberField K] (m : G1 K 2) (t : ℝ) :
    retractOne ((m : AdelicGLn.AdelicGL K 2) * zt K t) = m := by
  have h : detModule K 2 ((m : AdelicGLn.AdelicGL K 2) * zt K t) = ⟨Real.exp t, Real.exp_pos t⟩ := by
    rw [map_mul, mem_normOneGL_iff_detModule.1 m.2, one_mul, zt, detModule_centralSection two_pos]
  refine Subtype.ext ?_
  rw [coe_retractOne, h]
  exact mul_inv_cancel_right _ _

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.levProj :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (S : Subgroup (G1 K (2 + 2))) (π : S →* G1 K 2 × G1 K 2), IsClosed (S : Set (G1 K (2 + 2))) ∧ Continuous π ∧
      (∀ g, g ∈ S ↔ ∃ X m₁ m₂ t, g = nn X * lv m₁ m₂ t) ∧ ∀ X m₁ m₂ t (p : S), (p : G1 K (2 + 2)) = nn X * lv m₁ m₂ t → π p = (m₁, m₂) := by
  intro K _ _
  obtain ⟨S, ν, hS, -, hmem, -⟩ := parHaar (K := K) (Measure.haar)
  obtain ⟨hlv, hmul, hone, -⟩ := blkLaws (K := K)
  obtain ⟨-, -, hinj, -⟩ := pkLaws (K := K)
  have hp : ∀ p : S, ∃ X m₁ m₂ t, (p : G1 K (2 + 2)) = nn X * lv m₁ m₂ t := fun p => (hmem p).1 p.2
  choose X m₁ m₂ t hX using hp
  have hcomm : ∀ (a b : G1 K 2) (u : ℝ) Y, ∃ Z, lv a b u * nn Y = nn Z * lv a b u := by
    intro a b u Y
    obtain ⟨e, he, -⟩ := adMeas a b u
    exact ⟨e.symm Y, by rw [he, e.apply_symm_apply]⟩
  have hprod : ∀ p q : S, m₁ (p * q) = m₁ p * m₁ q ∧ m₂ (p * q) = m₂ p * m₂ q := by
    intro p q
    obtain ⟨Z, hZ⟩ := hcomm (m₁ p) (m₂ p) (t p) (X q)
    have h : nn (X (p * q)) * lv (m₁ (p * q)) (m₂ (p * q)) (t (p * q)) =
        nn (X p + Z) * lv (m₁ p * m₁ q) (m₂ p * m₂ q) (t p + t q) := by
      rw [← hX, Subgroup.coe_mul, hX p, hX q, mul_assoc, ← mul_assoc (lv _ _ _), hZ, mul_assoc, hmul, ← mul_assoc]
      exact congrArg (· * _) (unipOne_add 2 _ _).symm
    obtain ⟨-, h1, h2, -⟩ := hinj _ _ _ _ _ _ _ _ h
    exact ⟨h1, h2⟩
  have hunit : ∀ (Y : UPos (2 + 2) 2 → 𝔸[K]) (a b : G1 K 2) (u : ℝ) (p : S), (p : G1 K (2 + 2)) = nn Y * lv a b u →
      m₁ p = a ∧ m₂ p = b := by
    intro Y a b u p h
    obtain ⟨-, h1, h2, -⟩ := hinj _ _ _ _ _ _ _ _ ((hX p).symm.trans h)
    exact ⟨h1, h2⟩
  let π : S →* G1 K 2 × G1 K 2 :=
    { toFun := fun p => (m₁ p, m₂ p)
      map_one' := by
        obtain ⟨h1, h2⟩ := hunit 0 1 1 0 1 (by rw [hone, mul_one]; exact (unipOne_zero 2).symm)
        exact Prod.ext h1 h2
      map_mul' := fun p q => Prod.ext (hprod p q).1 (hprod p q).2 }
  let F : G1 K (2 + 2) → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔸[K] := fun g =>
    (g : AdelicGLn.AdelicGL K (2 + 2)).val.submatrix finSumFinEquiv finSumFinEquiv
  have hF : Continuous F := (Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _
  let A : S → AdelicGLn.AdelicGL K 2 := fun p => (m₁ p : AdelicGLn.AdelicGL K 2) * zt K (t p)
  let D : S → AdelicGLn.AdelicGL K 2 := fun p => (m₂ p : AdelicGLn.AdelicGL K 2) * zt K (-t p)
  have hblk : ∀ p : S, ∃ B, F p = Matrix.fromBlocks (A p).val B 0 (D p).val := by
    intro p
    obtain ⟨B, hB⟩ := unip_blk' (X p) (A p) (D p)
    refine ⟨B, ?_⟩
    rw [← hB]
    simp only [F, hX p, Subgroup.coe_mul, hlv, coe_unipOne, A, D]
  have hFinv : ∀ p : S, F (p : G1 K (2 + 2)) * F ((p⁻¹ : S) : G1 K (2 + 2)) = 1 := by
    intro p
    simp only [F, Matrix.submatrix_mul_equiv, Subgroup.coe_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.submatrix_one_equiv]
  have hinv : ∀ p : S, (A p)⁻¹ = A p⁻¹ ∧ (D p)⁻¹ = D p⁻¹ := by
    intro p
    obtain ⟨B, hB⟩ := hblk p
    obtain ⟨B', hB'⟩ := hblk p⁻¹
    have e := hFinv p
    rw [hB, hB', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at e
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at e
    exact ⟨(eq_inv_of_mul_eq_one_right (Units.ext e.1)).symm, (eq_inv_of_mul_eq_one_right (Units.ext e.2.2.2)).symm⟩
  have hF₁ : Continuous fun p : S => F (p : G1 K (2 + 2)) := hF.comp continuous_subtype_val
  have hF₂ : Continuous fun p : S => F ((p⁻¹ : S) : G1 K (2 + 2)) := hF₁.comp continuous_inv
  have hA : Continuous A := Units.continuous_iff.2
    ⟨(hF₁.matrix_submatrix Sum.inl Sum.inl).congr fun p => by
        obtain ⟨B, hB⟩ := hblk p
        show (F p).toBlocks₁₁ = _
        rw [hB]; rfl,
      (hF₂.matrix_submatrix Sum.inl Sum.inl).congr fun p => by
        obtain ⟨B, hB⟩ := hblk p⁻¹
        show (F (p⁻¹ : S)).toBlocks₁₁ = _
        rw [hB, ← (hinv p).1]; rfl⟩
  have hD : Continuous D := Units.continuous_iff.2
    ⟨(hF₁.matrix_submatrix Sum.inr Sum.inr).congr fun p => by
        obtain ⟨B, hB⟩ := hblk p
        show (F p).toBlocks₂₂ = _
        rw [hB]; rfl,
      (hF₂.matrix_submatrix Sum.inr Sum.inr).congr fun p => by
        obtain ⟨B, hB⟩ := hblk p⁻¹
        show (F (p⁻¹ : S)).toBlocks₂₂ = _
        rw [hB, ← (hinv p).2]; rfl⟩
  have hπ : Continuous π :=
    ((continuous_retractOne.comp hA).prodMk (continuous_retractOne.comp hD)).congr fun p =>
      Prod.ext (ret_zt _ _) (ret_zt _ _)
  refine ⟨S, π, hS, hπ, hmem, fun Y a b u p h => ?_⟩
  obtain ⟨h1, h2⟩ := hunit Y a b u p h
  exact Prod.ext h1 h2
