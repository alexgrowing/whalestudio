import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.LinAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.AdMeas

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem vL (i : Fin 2) : ((finSumFinEquiv (Sum.inl i : Fin 2 ⊕ Fin 2) : Fin (2 + 2)) : ℕ) = i := rfl

private theorem vR (i : Fin 2) : ((finSumFinEquiv (Sum.inr i : Fin 2 ⊕ Fin 2) : Fin (2 + 2)) : ℕ) = 2 + i := rfl

private theorem exBlock {R : Type} [CommRing R] (C : Matrix (Fin 2) (Fin 2) R) :
    ∃ Z : UPos (2 + 2) 2 → R,
      unipMatrix Z = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 C 0 1) := by
  refine ⟨fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 C 0 (1 : Matrix (Fin 2) (Fin 2) R)) p.1.1 p.1.2, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [unipMatrix, blockEntry_apply, Matrix.one_apply, Fin.ext_iff, vL, vR]

private theorem triang {R : Type} [CommRing R] (a d : GL (Fin 2) R) (C : Matrix (Fin 2) (Fin 2) R) :
    ∃ Z : UPos (2 + 2) 2 → R,
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks a.val C 0 d.val) = (unipGL Z * blk a d).val := by
  obtain ⟨Z, hZ⟩ := exBlock (C * (d⁻¹).val)
  refine ⟨Z, ?_⟩
  rw [Units.val_mul, coe_unipGL, hZ]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_assoc, Units.inv_mul]

private theorem bigCell {F : Type} [Field F] (g : GL (Fin (2 + 2)) F)
    (h : ((g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det ≠ 0) :
    ∃ ξ : UPos (2 + 2) 2 → F, ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
      (g * (unipGL ξ)⁻¹ * (wGL F)⁻¹).val i j = 0 := by
  obtain ⟨M, hM⟩ := (Matrix.reindex (finSumFinEquiv (m := 2) (n := 2)) (finSumFinEquiv (m := 2) (n := 2))).surjective g.val
  rw [← Matrix.fromBlocks_toBlocks M] at hM
  have hC : (g : Matrix (Fin (2 + 2)) (Fin (2 + 2)) F).submatrix (Fin.natAdd 2) (Fin.castAdd 2) = M.toBlocks₂₁ := by
    rw [← hM]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
      finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁]
  rw [hC] at h
  obtain ⟨Z, hZ⟩ := exBlock (-(M.toBlocks₂₁⁻¹ * M.toBlocks₂₂))
  refine ⟨-Z, fun i j hi hj => ?_⟩
  have hw : ((wGL F)⁻¹).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) F) 1 0) := rfl
  rw [Units.val_mul, Units.val_mul, coe_unipGL_inv, neg_neg, hZ, hw, ← hM]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h), Matrix.one_mul, neg_add_cancel]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [vL] at hi; omega
  · rw [vL] at hi; omega
  · simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · rw [vR] at hj; omega

private theorem oneInt {K : Type} [Field K] [NumberField K] (f : (UPos 2 1 → 𝔸[K]) → ℂ) :
    ∫ y in GroundTheory.Global.fundamentalSet K, f (fun _ => y) ∂GroundTheory.Global.adeleMeasure K =
      ∫ Y in unipFundamentalDomain K 2 1, f Y ∂unipMeasure K 2 1 := by
  letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  have hm : MeasurePreserving (MeasurableEquiv.funUnique (UPos 2 1) 𝔸[K]) (unipMeasure K 2 1) (GroundTheory.Global.adeleMeasure K) := by
    convert measurePreserving_funUnique (GroundTheory.Global.adeleMeasure K) (UPos 2 1)
  rw [← hm.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
  congr 1
  · congr 1
    ext Y
    simp [unipFundamentalDomain, Unique.forall_iff]
  · funext Y
    congr 1
    funext p
    simp [Subsingleton.elim p default]

private theorem ratOne {K : Type} [Field K] [NumberField K] {n : ℕ} (g : GL (Fin n) K) :
    ∃ γ : Gam K n, ((γ : G1 K n) : AdelicGLn.AdelicGL K n) = AdelicGLn.diagonal K n g :=
  ⟨⟨⟨_, rationalGL_le_normOneGL ⟨g, rfl⟩⟩, ⟨g, rfl⟩⟩, rfl⟩

private theorem coeLv {K : Type} [Field K] [NumberField K] (a d : G1 K 2) :
    ((lv a d 0 : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = blk (a : AdelicGLn.AdelicGL K 2) (d : AdelicGLn.AdelicGL K 2) := by
  have hz : zt K 0 = 1 := by
    have : (⟨Real.exp 0, Real.exp_pos 0⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext Real.exp_zero
    rw [zt, this, map_one]
  rw [blkLaws.1, neg_zero, hz, mul_one, mul_one]

private theorem uMat {R : Type} [CommRing R] (y : R) :
    unipMatrix (fun _ : UPos 2 1 => y) = 1 + y • Matrix.single 0 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unipMatrix, blockEntry_apply]

private theorem conjMat {K : Type} [Field K] [NumberField K] {r : ℕ} (g : GL (Fin (2 + 2)) K) (X₀ : UPos (2 + 2) r → K)
    (A C D : Matrix (Fin 2) (Fin 2) K)
    (h : g.val * blockEntry X₀ * (g⁻¹).val = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 D)) (y : 𝔸[K]) :
    (AdelicGLn.diagonal K _ g * unipGL (fun p => y * algebraMap K 𝔸[K] (X₀ p)) * (AdelicGLn.diagonal K _ g)⁻¹).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (1 + y • (algebraMap K 𝔸[K]).mapMatrix A)
        (y • C.map (algebraMap K 𝔸[K])) 0 (1 + y • (algebraMap K 𝔸[K]).mapMatrix D)) := by
  have hb : blockEntry (fun p => y * algebraMap K 𝔸[K] (X₀ p)) = y • (algebraMap K 𝔸[K]).mapMatrix (blockEntry X₀) := by
    ext i j
    simp only [blockEntry_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul]
    split_ifs <;> simp
  have hd : ∀ u : GL (Fin (2 + 2)) K, (AdelicGLn.diagonal K _ u).val = (algebraMap K 𝔸[K]).mapMatrix u.val := fun _ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, coe_unipGL, unipMatrix, hb, hd, hd, mul_add, add_mul, mul_one, ← map_mul,
    Units.mul_inv, map_one, Matrix.mul_smul, Matrix.smul_mul, ← map_mul, ← map_mul, h]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

private theorem conjU {K : Type} [Field K] [NumberField K] (m : GL (Fin 2) K) (μ : G1 K 2)
    (hμ : (μ : AdelicGLn.AdelicGL K 2) = AdelicGLn.diagonal K 2 m) (y : 𝔸[K]) :
    ((μ⁻¹ * unipOne K 2 1 (fun _ => y) * μ : G1 K 2) : AdelicGLn.AdelicGL K 2).val =
      1 + y • (algebraMap K 𝔸[K]).mapMatrix ((m⁻¹).val * Matrix.single 0 1 1 * m.val) := by
  have hd : ∀ u : GL (Fin 2) K, (AdelicGLn.diagonal K _ u).val = (algebraMap K 𝔸[K]).mapMatrix u.val := fun _ => rfl
  have hs : (algebraMap K 𝔸[K]).mapMatrix (Matrix.single (0 : Fin 2) 1 1) = Matrix.single 0 1 1 := by
    simp [Matrix.map_single]
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hμ, ← map_inv, coe_unipOne, Units.val_mul, Units.val_mul, coe_unipGL,
    uMat, hd, hd, mul_add, add_mul, mul_one, ← map_mul, Units.inv_mul, map_one, Matrix.mul_smul, Matrix.smul_mul,
    map_mul, map_mul, hs]

private theorem fromMat {K : Type} [Field K] [NumberField K] (γ u : G1 K (2 + 2)) (a d : G1 K 2) (C : Matrix (Fin 2) (Fin 2) 𝔸[K])
    (h : ((γ : AdelicGLn.AdelicGL K (2 + 2)) * (u : AdelicGLn.AdelicGL K (2 + 2)) * (γ : AdelicGLn.AdelicGL K (2 + 2))⁻¹).val =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (a : AdelicGLn.AdelicGL K 2).val C 0 (d : AdelicGLn.AdelicGL K 2).val)) :
    ∃ Z, γ * u = nn Z * (lv a d 0 * γ) := by
  obtain ⟨Z, hZ⟩ := triang (a : AdelicGLn.AdelicGL K 2) (d : AdelicGLn.AdelicGL K 2) C
  refine ⟨Z, ?_⟩
  rw [← mul_assoc, ← mul_inv_eq_iff_eq_mul]
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, h, hZ, Subgroup.coe_mul, coeLv, coe_unipOne]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.dies :
    ∀ {K : Type} [Field K] [NumberField K] (F : G1 K (2 + 2) → ℂ), PFun F → ∀ (γ : Gam K (2 + 2)) (r : ℕ), (r = 1 ∨ r = 3 ∨ (r = 2 ∧ γ ∉ ParΓ K 2 2 ∧
        ¬ ∃ δ ∈ PK K, ∃ ξ : unipLattice K (2 + 2) 2, (γ : G1 K (2 + 2)) = δ * w0 K * nn ξ.1)) → ∃ X₀, Dies F r γ X₀ := by
  intro K _ _ F hF γ r hr
  obtain ⟨g, hg⟩ : ∃ g, AdelicGLn.diagonal K (2 + 2) g = ((γ : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := γ.2
  have hmul := (blkLaws (K := K)).2.1
  have hP : ∀ a d : Gam K 2, lv (a : G1 K 2) (d : G1 K 2) 0 ∈ PK K := fun a d =>
    ((pkLaws (K := K)).2.1 _).2 ⟨0, a, d, by
      rw [show nn (0 : unipLattice K (2 + 2) 2).1 = 1 from unipOne_zero 2, one_mul]⟩
  obtain ⟨X₀, m, C, hC⟩ := linAlg g r (by
    rcases hr with h | h | ⟨h, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨h, fun h0 => h1 ?_, by_contra fun h0 => h2 ?_⟩)
    · refine Subgroup.subset_closure fun i j hi hj => ?_
      rw [← hg, AdelicGLn.diagonal_apply]
      have := congrFun (congrFun h0 ⟨i - 2, by omega⟩) ⟨j, hj⟩
      rw [Matrix.submatrix_apply, show Fin.natAdd 2 (⟨i - 2, by omega⟩ : Fin 2) = i from Fin.ext (by simp; omega),
        show Fin.castAdd 2 (⟨j, hj⟩ : Fin 2) = j from Fin.ext rfl] at this
      rw [this, Matrix.zero_apply, map_zero]
    · obtain ⟨ξ, hξ⟩ := bigCell g h0
      obtain ⟨δ, hδ⟩ := ratOne (g * (unipGL ξ)⁻¹ * (wGL K)⁻¹)
      have hw : AdelicGLn.diagonal K (2 + 2) (wGL K) = wGL 𝔸[K] := by
        ext i j
        obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
        obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
        rw [AdelicGLn.diagonal_apply]
        rcases i with i | i <;> rcases j with j | j <;> simp [wGL, Matrix.one_apply]
      refine ⟨δ, ⟨δ, Subgroup.subset_closure fun i j hi hj => ?_, rfl⟩,
        ⟨fun p => algebraMap K 𝔸[K] (ξ p), ξ, rfl⟩, Subtype.ext ?_⟩
      · rw [hδ, AdelicGLn.diagonal_apply, hξ i j hi hj, map_zero]
      · rw [Subgroup.coe_mul, Subgroup.coe_mul, hδ, (blkLaws (K := K)).2.2.2.2.2.2.1, coe_unipOne, ← hw, ← diagonal_unipGL,
          ← map_mul, ← map_mul, ← hg, inv_mul_cancel_right, inv_mul_cancel_right])
  obtain ⟨μ, hμ⟩ := ratOne m
  refine ⟨X₀, fun x => ?_⟩
  rcases hC with hC | hC
  · rw [← hF.cusp₂ (lv 1 (μ : G1 K 2) 0 * (γ : G1 K (2 + 2)) * x), ← oneInt]
    congr 1
    funext y
    obtain ⟨Z, hZ⟩ := fromMat γ (unipOne K (2 + 2) r fun p => y * algebraMap K 𝔸[K] (X₀ p)) 1
      ((μ : G1 K 2)⁻¹ * unipOne K 2 1 (fun _ => y) * μ) (y • C.map (algebraMap K 𝔸[K])) (by
        rw [← hg, coe_unipOne, conjMat g X₀ _ _ _ hC, conjU m μ hμ]
        simp)
    rw [hZ, mul_assoc, hF.unip, ← hF.rat _ (hP 1 μ)]
    simp only [← mul_assoc, hmul, OneMemClass.coe_one, mul_inv_cancel, one_mul, add_zero]
  · rw [← hF.cusp₁ (lv (μ : G1 K 2) 1 0 * (γ : G1 K (2 + 2)) * x), ← oneInt]
    congr 1
    funext y
    obtain ⟨Z, hZ⟩ := fromMat γ (unipOne K (2 + 2) r fun p => y * algebraMap K 𝔸[K] (X₀ p))
      ((μ : G1 K 2)⁻¹ * unipOne K 2 1 (fun _ => y) * μ) 1 (y • C.map (algebraMap K 𝔸[K])) (by
        rw [← hg, coe_unipOne, conjMat g X₀ _ _ _ hC, conjU m μ hμ]
        simp)
    rw [hZ, mul_assoc, hF.unip, ← hF.rat _ (hP μ 1)]
    simp only [← mul_assoc, hmul, OneMemClass.coe_one, mul_inv_cancel, one_mul, add_zero]
