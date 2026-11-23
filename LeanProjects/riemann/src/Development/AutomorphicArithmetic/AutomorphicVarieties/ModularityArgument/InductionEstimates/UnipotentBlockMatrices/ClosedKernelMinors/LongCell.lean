import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.SubDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.AutomorphicForms.ReductionIdele

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lc_inv_compact {K : Type} [Field K] [NumberField K] {B : Set 𝔸[K]} (hB : IsCompact B) {a : ℝ} (ha : 0 < a) :
    ∃ T : Set 𝔸[K], IsCompact T ∧ ∀ u : GroundTheory.Global.IdeleGroup K, (u : 𝔸[K]) ∈ B →
      a ≤ (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) → (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ 1 →
      ((u⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
  obtain ⟨S, hS, hc⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) ha 1
  have hci : Continuous fun s : GroundTheory.Global.IdeleGroup K => ((s⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) :=
    Units.continuous_coe_inv
  have hE : IsCompact ((fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K => p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) '' (B ×ˢ S)) :=
    (hB.prod hS).image (continuous_fst.mul (hci.comp continuous_snd))
  haveI := GroundTheory.Global.t2Space_adeleRing K
  haveI := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hF := ((GroundTheory.Global.isClosed_principalSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hE).finite_of_discrete
  have hF2 := hF.image (fun x : AdeleRing.principalSubgroup (𝓞 K) K => Ring.inverse (x : 𝔸[K]))
  refine ⟨_, (hF2.isCompact.prod hS).image (f := fun p : 𝔸[K] × GroundTheory.Global.IdeleGroup K =>
    p.1 * ((p.2⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K])) (continuous_fst.mul (hci.comp continuous_snd)), fun u hu h1 h2 => ?_⟩
  obtain ⟨c, hcS⟩ := hc u h1 h2
  set d := GroundTheory.Global.IdeleGroup.diagonal K c with hd
  have hmem : ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
    rw [hd, ← map_inv]
    exact ⟨((c⁻¹ : Kˣ) : K), rfl⟩
  refine ⟨((d : 𝔸[K]), d * u), ⟨⟨⟨_, hmem⟩, ⟨((u : 𝔸[K]), d * u), ⟨hu, hcS⟩, ?_⟩, ?_⟩, hcS⟩, ?_⟩
  · change (u : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv_rev, mul_inv_cancel_left]
  · change Ring.inverse ((d⁻¹ : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) = _
    rw [Ring.inverse_unit, inv_inv]
  · change (d : 𝔸[K]) * _ = _
    rw [← Units.val_mul, mul_inv, mul_inv_cancel_left]

private theorem lc_rows {R : Type} [CommRing R] (X Y : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : GL (Fin (2 + 2)) R)
    (h : wGL R * unipGL X = unipGL Y * blk a b * k) :
    b.val * k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  have hL : ∀ (i : Fin 2) (j : Fin (2 + 2)), (wGL R * unipGL X).val (Fin.natAdd 2 i) j = unipMatrix X (Fin.castAdd 2 i) j := by
    intro i j
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [wGL, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero, coe_unipGL, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hU : ∀ (i : Fin 2) (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (j : Fin (2 + 2)),
      (unipMatrix Y * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro i M j
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dif_neg (by simp), zero_mul]
  have hR : ∀ (i : Fin 2) (j : Fin (2 + 2)), (unipGL Y * blk a b * k).val (Fin.natAdd 2 i) j =
      ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j := by
    intro i j
    rw [mul_assoc, Units.val_mul, coe_unipGL, hU, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add]
    simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
      finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
      Finset.sum_const_zero, zero_add]
  have key : ∀ (i : Fin 2) (j : Fin (2 + 2)), ∑ l, b.val i l * k.val (Fin.natAdd 2 l) j = unipMatrix X (Fin.castAdd 2 i) j :=
    fun i j => by rw [← hL, h, hR]
  refine ⟨?_, fun i j hp => ?_⟩
  · ext i j
    rw [Matrix.mul_apply]
    refine (key i (Fin.castAdd 2 j)).trans ?_
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dif_neg (fun hh => absurd hh.2 (not_le.2 j.2)), add_zero]
    simp [Matrix.one_apply, Fin.ext_iff]
  · rw [Matrix.mul_apply]
    refine Eq.trans ?_ (key i (Fin.natAdd 2 j)).symm
    rw [unipMatrix, Matrix.add_apply, blockEntry_apply, dif_pos hp, Matrix.one_apply_ne, zero_add]
    intro e
    have := congrArg Fin.val e
    simp at this
    omega

private theorem lc_adj {R : Type} [CommRing R] (b c : Matrix (Fin 2) (Fin 2) R) (h : b * c = 1) :
    b = b.det • c.adjugate := by
  have h1 : c.adjugate = c.det • b := by
    have := congrArg (· * c.adjugate) h
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul] at this
    exact this.symm
  rw [h1, smul_smul, ← Matrix.det_mul, h, Matrix.det_one, one_smul]

private theorem lc_main {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (k : G1 K (2 + 2)) (hk : k ∈ KG K (2 + 2)) :
    ∃ (b : AdelicGLn.AdelicGL K 2), ∃ k' ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2))),
      (detModule K 2 b⁻¹).1 = Real.exp (HH (w0 K * nn X * k)) ∧ (detModule K 2 b⁻¹).1 ≤ 1 ∧
      b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1 ∧
      ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b.val * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j := by
  obtain ⟨Y, m₁, m₂, t, k', hk', e⟩ := iwa (w0 K * nn X)
  obtain ⟨h1, h2, -⟩ := hpSpec (K := K)
  obtain ⟨b1, -, -, -, -, -, b2, -⟩ := blkLaws (K := K)
  have hH : HH (w0 K * nn X * k) = t := by
    rw [(h2 k hk).2, e, h1, (h2 k' hk').1, add_zero]
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, b1, b2, coe_unipOne] at e'
  obtain ⟨r1, r2⟩ := lc_rows X Y _ _ _ e'
  refine ⟨(m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t), k', hk', ?_, ?_, r1, r2⟩
  · rw [hH, map_inv, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    change (Real.exp (-t))⁻¹ = _
    rw [Real.exp_neg, inv_inv]
  · have hs := subDet (2 + 2) (k' : AdelicGLn.AdelicGL K (2 + 2)) hk' (Fin.natAdd 2) (Fin.castAdd 2)
      (Fin.natAdd_injective 2 2) (Fin.castAdd_injective 2 2)
    exact hs.2.2 _ (Units.inv_eq_of_mul_eq_one_right r1)

private noncomputable def lcF {K : Type} [Field K] [NumberField K] (q : 𝔸[K] × AdelicGLn.AdelicGL K (2 + 2)) (p : UPos (2 + 2) 2) : 𝔸[K] :=
  q.1 * ((q.2.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).adjugate * q.2.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2))
    ⟨(p.1.1 : ℕ), p.2.1⟩ ⟨(p.1.2 : ℕ) - 2, by have := p.1.2.2; omega⟩

private theorem continuous_lower_left_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem continuous_lower_right_block {K : Type} [Field K] [NumberField K] :
    Continuous fun k : AdelicGLn.AdelicGL K (2 + 2) => k.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2) :=
  Units.continuous_val.matrix_submatrix _ _

private theorem lc_cont {K : Type} [Field K] [NumberField K] : Continuous (lcF (K := K)) := by
  refine continuous_pi fun p => ?_
  unfold lcF
  exact continuous_fst.mul (((continuous_lower_left_block.matrix_adjugate.matrix_mul continuous_lower_right_block).matrix_elem _ _).comp continuous_snd)

private theorem lc_eq {K : Type} [Field K] [NumberField K] (X : UPos (2 + 2) 2 → 𝔸[K]) (b : Matrix (Fin 2) (Fin 2) 𝔸[K])
    (k' : AdelicGLn.AdelicGL K (2 + 2)) (h3 : b * k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) = 1)
    (h4 : ∀ (i j : Fin 2) (hp), X ⟨(Fin.castAdd 2 i, Fin.natAdd 2 j), hp⟩ =
        (b * k'.val.submatrix (Fin.natAdd 2) (Fin.natAdd 2)) i j) : X = lcF (b.det, k') := by
  funext p
  obtain ⟨⟨i, j⟩, hi, hj⟩ := p
  have hj2 := j.2
  have hi' : (i : ℕ) < 2 := hi
  have hj' : 2 ≤ (j : ℕ) := hj
  obtain ⟨i, rfl⟩ : ∃ i' : Fin 2, i = Fin.castAdd 2 i' := ⟨⟨i, hi'⟩, Fin.ext rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j' : Fin 2, j = Fin.natAdd 2 j' := ⟨⟨(j : ℕ) - 2, by omega⟩, Fin.ext (by simp; omega)⟩
  have hb := lc_adj _ _ h3
  rw [h4 i j]
  conv_lhs => rw [hb]
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  simp [lcF]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.longCell :
    ∀ {K : Type} [Field K] [NumberField K], (∀ (X : UPos (2 + 2) 2 → 𝔸[K]), ∀ k ∈ KG K (2 + 2), HH (w0 K * nn X * k) ≤ 0) ∧
      ∀ R : ℝ, ∃ C : Set (UPos (2 + 2) 2 → 𝔸[K]), IsCompact C ∧ ∀ X, ∀ k ∈ KG K (2 + 2), -R ≤ HH (w0 K * nn X * k) → X ∈ C := by
  intro K _ _
  refine ⟨fun X k hk => ?_, fun R => ?_⟩
  · obtain ⟨b, k', -, h1, h2, -⟩ := lc_main X k hk
    rw [h1] at h2
    exact Real.exp_le_one_iff.1 h2
  have hB : IsCompact ((fun k : AdelicGLn.AdelicGL K (2 + 2) => (k.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2)).det) ''
      (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))) :=
    (isCompact_maxCompact (K := K) (n := 2 + 2)).image continuous_lower_left_block.matrix_det
  obtain ⟨T, hT, hu⟩ := lc_inv_compact hB (Real.exp_pos (-R))
  refine ⟨lcF '' (T ×ˢ (maxCompact : Subgroup (AdelicGLn.AdelicGL K (2 + 2)))),
    (hT.prod (isCompact_maxCompact (K := K) (n := 2 + 2))).image lc_cont, fun X k hk hR => ?_⟩
  obtain ⟨b, k', hk', h1, h2, h3, h4⟩ := lc_main X k hk
  have hinv : ((b⁻¹ : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]) = k'.val.submatrix (Fin.natAdd 2) (Fin.castAdd 2) :=
    Units.inv_eq_of_mul_eq_one_right h3
  have hmem : ((AdelicGLn.det K 2 b : GroundTheory.Global.IdeleGroup K) : 𝔸[K]) ∈ T := by
    have h5 := hu (AdelicGLn.det K 2 b⁻¹) ⟨k', hk', by rw [AdelicGLn.coe_det, hinv]⟩
      ((Real.exp_le_exp.2 hR).trans h1.ge) h2
    rwa [← map_inv, inv_inv] at h5
  rw [AdelicGLn.coe_det] at hmem
  exact ⟨(_, k'), ⟨hmem, hk'⟩, (lc_eq X b.val k' h3 h4).symm⟩
