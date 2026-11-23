import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PluckOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.UnipBlocks
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal
import GroundTheory.GlobalFields.IdeleGroups.UnitBound
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem lf_fin {K : Type} [Field K] [NumberField K] {S : Set 𝔸[K]} (hS : IsCompact S) :
    {k : K | algebraMap K 𝔸[K] k ∈ S}.Finite := by
  have h1 := GroundTheory.Global.discreteTopology_principalSubgroup K
  have h2 := GroundTheory.Global.isClosed_principalSubgroup K
  have h3 : IsCompact ((Subtype.val : NumberField.AdeleRing.principalSubgroup (𝓞 K) K → 𝔸[K]) ⁻¹' S) :=
    h2.isClosedEmbedding_subtypeVal.isCompact_preimage hS
  have h4 := h3.finite_of_discrete
  refine Set.Finite.of_finite_image (f := algebraMap K 𝔸[K]) ((h4.image Subtype.val).subset ?_)
    (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K).injOn
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨⟨_, k, rfl⟩, hk, rfl⟩

private theorem lf_ray (K : Type) [Field K] [NumberField K] (T : ℝ) :
    ∃ Z : Set 𝔸[K], IsCompact Z ∧ ∀ t, T ≤ t →
      ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det ∈ Z := by
  set e : ℝ := (((2 : ℕ) : ℝ) * Module.finrank ℚ K)⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  let B : Set (InfiniteAdeleRing K) :=
    Set.univ.pi fun w : InfinitePlace K => Metric.closedBall (0 : w.Completion) (Real.exp (-T) ^ e)
  have hB : IsCompact B := isCompact_univ_pi fun w => isCompact_closedBall _ _
  let Z0 : Set 𝔸[K] := B ×ˢ ({1} : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
  have hZ0 : IsCompact Z0 := hB.prod isCompact_singleton
  refine ⟨(fun x => x * x) '' Z0, hZ0.image (continuous_id.mul continuous_id), fun t ht => ?_⟩
  have hp : 0 < Real.exp (-t) ^ e := Real.rpow_pos_of_pos (Real.exp_pos _) e
  refine ⟨(posIdele (K := K) _ hp : GroundTheory.Global.IdeleGroup K), ⟨fun w _ => ?_, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_posIdele_infinite]
    exact Real.rpow_le_rpow (Real.exp_pos _).le (Real.exp_le_exp.2 (by linarith)) he0
  · exact DFunLike.ext _ _ fun v => posIdele_finite _ hp v
  · rw [← AdelicGLn.coe_det]
    have : zt K (-t) = diagUnits 2 fun _ => posIdele (K := K) _ hp := rfl
    rw [this, det_diagUnits, Fin.prod_univ_two, Units.val_mul]

private theorem lf_minor {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R)
    (h : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (c : Fin 2 → Fin (2 + 2)) :
    ((unipMatrix X * (blk a b).val * h).submatrix (Fin.natAdd 2) c).det =
      b.val.det * (h.submatrix (Fin.natAdd 2) c).det := by
  rw [← Matrix.det_mul]
  congr 1
  ext i j
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (k : Fin (2 + 2)),
      (unipMatrix X * M) (Fin.natAdd 2 i) k = M (Fin.natAdd 2 i) k := by
    intro M k
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [blockEntry_apply, dif_neg, zero_mul]
    simp
  rw [Matrix.submatrix_apply, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.locFin :
    ∀ {K : Type} [Field K] [NumberField K] (C : Set (G1 K (2 + 2))) (T : ℝ), IsCompact C → {q : Cos K | ∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)}.Finite := by
  intro K _ _ C T hC
  obtain ⟨D, hD, -, hxD⟩ := GroundTheory.Global.IdeleGroup.exists_isCompact_normOneSubgroup K
  obtain ⟨Z, hZ, hzZ⟩ := lf_ray K T
  have hK : IsCompact (KG K (2 + 2) : Set (G1 K (2 + 2))) := ((blkLaws (K := K)).2.2.2.2.2.2.2.2.2.2.2 _).1
  let mn : (Fin 2 → Fin (2 + 2)) → G1 K (2 + 2) → 𝔸[K] := fun c g =>
    (((g : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det
  have hmn : ∀ c, Continuous (mn c) := fun c =>
    ((Units.continuous_val.comp continuous_subtype_val).matrix_submatrix _ _).matrix_det
  let Φ : (Fin 2 → Fin (2 + 2)) → GroundTheory.Global.IdeleGroup K × 𝔸[K] × G1 K (2 + 2) × G1 K (2 + 2) → 𝔸[K] :=
    fun c p => (p.1 : 𝔸[K]) * p.2.1 * mn c (p.2.2.1 * p.2.2.2⁻¹)
  have hΦ : ∀ c, Continuous (Φ c) := fun c =>
    ((Units.continuous_val.comp continuous_fst).mul continuous_snd.fst).mul
      ((hmn c).comp (continuous_snd.snd.fst.mul continuous_snd.snd.snd.inv))
  have hfin : ∀ c, {k : K | algebraMap K 𝔸[K] k ∈ Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C)}.Finite :=
    fun c => lf_fin ((hD.prod (hZ.prod (hK.prod hC))).image (hΦ c))
  have hrat : ∀ q : Cos K, ∃ γ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) γ =
      ((q.out : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) := fun q => q.out.2
  choose γ hγ using hrat
  have hm : ∀ q c, mn c (q.out : G1 K (2 + 2)) =
      algebraMap K 𝔸[K] ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det := by
    intro q c
    simp only [mn]
    rw [← hγ, RingHom.map_det]
    rfl
  have key : ∀ q : Cos K, (∃ g ∈ C, T ≤ HH ((q.out : G1 K (2 + 2)) * g)) → ∃ a : Kˣ, ∀ c,
      algebraMap K 𝔸[K] (a * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det) ∈
        Φ c '' (D ×ˢ Z ×ˢ (KG K (2 + 2) : Set (G1 K (2 + 2))) ×ˢ C) := by
    rintro q ⟨g, hg, hT⟩
    obtain ⟨X, m₁, m₂, t, k, hk, hq⟩ := iwa ((q.out : G1 K (2 + 2)) * g)
    rw [hq, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero] at hT
    have hm2 : AdelicGLn.det K 2 (m₂ : AdelicGLn.AdelicGL K 2) ∈ GroundTheory.Global.IdeleGroup.normOneSubgroup K :=
      mem_normOneGL_iff_detModule.1 m₂.2
    obtain ⟨a, ha⟩ := hxD _ hm2
    refine ⟨a, fun c => ⟨⟨_, ((zt K (-t) : AdelicGLn.AdelicGL K 2) : Matrix (Fin 2) (Fin 2) 𝔸[K]).det, k, g⟩, ⟨ha, hzZ t hT, hk, hg⟩, ?_⟩⟩
    have hq' : (q.out : G1 K (2 + 2)) = nn X * lv m₁ m₂ t * (k * g⁻¹) := by
      rw [← mul_assoc, ← hq, mul_inv_cancel_right]
    rw [map_mul, ← hm, hq']
    simp only [Φ, mn]
    rw [Subgroup.coe_mul _ (nn X * _), Subgroup.coe_mul _ (nn X), (blkLaws (K := K)).1, Units.val_mul (_ * blk _ _),
      Units.val_mul _ (blk _ _), coe_unipOne, coe_unipGL, lf_minor, Units.val_mul, Units.val_mul (m₂ : AdelicGLn.AdelicGL K 2),
      Matrix.det_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.coe_det]
    ring
  choose! a ha using key
  refine Set.Finite.of_finite_image
    (f := fun q c => (a q : K) * ((γ q : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det)
    ((Set.Finite.pi' hfin).subset ?_) ?_
  · rintro _ ⟨q, hq, rfl⟩ c
    exact ha q hq c
  · intro q _ q' _ h
    have h1 := (pluck (γ q') (γ q)).2 (((a q')⁻¹ * a q : Kˣ) : K) fun c => by
      have := congrFun h c
      simp only at this
      rw [Units.val_mul, mul_assoc, this, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← q.out_eq, ← q'.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    rw [(pkLaws (K := K)).1]
    intro i j hi hj
    have h2 : (((q'.out * q.out⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) =
        AdelicGLn.diagonal K (2 + 2) (γ q' * (γ q)⁻¹) := by
      rw [map_mul, map_inv, hγ, hγ]; rfl
    rw [h2]
    have h3 := AdelicGLn.diagonal_apply K (2 + 2) (γ q' * (γ q)⁻¹) i j
    rw [h1 i j hi hj, map_zero] at h3
    exact h3
