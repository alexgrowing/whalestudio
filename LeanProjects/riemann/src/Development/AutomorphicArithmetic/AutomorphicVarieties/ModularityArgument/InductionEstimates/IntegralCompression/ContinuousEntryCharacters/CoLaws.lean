import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.ContinuousEntryCharacters.LongWeylSwapsBlockDiagonal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BlkInvVal

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]

private theorem haar {n : ℕ} {U : Type} [Group U] [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U]
    (e : archCompact K n ≃ₜ* (ι → U)) (ν : Measure U) [IsProbabilityMeasure ν] (hl : ∀ k, MeasurePreserving (k * ·) ν ν)
    (hr : ∀ k, MeasurePreserving (· * k) ν ν) : IsHaarK (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := by
  have hm : Measurable e.symm := e.symm.continuous.measurable
  have hE : MeasurePreserving e.symm (Measure.pi fun _ : ι => ν) (Measure.map e.symm (Measure.pi fun _ : ι => ν)) := ⟨hm, rfl⟩
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, fun k => ?_, fun k => ?_⟩
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hl (e k i)) (fun x => ?_) (continuous_mul_left k).measurable
    change e.symm (e k * x) = _
    rw [map_mul, e.symm_apply_apply]
  · refine hE.of_semiconj (measurePreserving_pi _ _ fun i => hr (e k i)) (fun x => ?_) (continuous_mul_right k).measurable
    change e.symm (x * e k) = _
    rw [map_mul, e.symm_apply_apply]

private theorem coe_arc {n : ℕ} (k : archCompact K n) :
    ((arc1 k : G1 K n) : AdelicGLn.AdelicGL K n) = infEmb K n (k : archGroup K n) := by
  rw [arc1, ← retract_infEmb]
  exact congrArg Subtype.val (retractOne_coe (⟨_, maxCompact_le_normOneGL k.2⟩ : normOneGL K n))

private theorem zt0 : zt K 0 = 1 := by
  rw [zt, ← map_one (centralSection K 2)]
  exact congrArg _ (Subtype.ext Real.exp_zero)

private theorem inf_fst {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n x a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from (x.1 : ArchMatrix K n)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_infEmb]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

private theorem inf_snd {n : ℕ} (x : archGroup K n) (a b : Fin n) :
    (infEmb K n x a b).2 = (1 : Matrix (Fin n) (Fin n) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) a b := by
  rw [← AdelicGLn.prodEquiv_apply_snd, prodEquiv_infEmb]
  rfl

omit [Fintype ι] in
private theorem ent (C : Co K ι) {n : ℕ} (x : ι → unitaryGroup (Fin n) ℂ) (i : ι) (a b : Fin n) :
    C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K (infEmb K n ((C.Φ n).symm x : archCompact K n) a b).1) i =
      (x i : Matrix (Fin n) (Fin n) ℂ) a b := by
  rw [inf_fst, ← C.Ψ_val, ← C.Φ_val, ContinuousMulEquiv.apply_symm_apply]

omit [Fintype ι] in
private theorem blkA (C : Co K ι) (a b : ι → U2) :
    lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i)) := by
  apply Subtype.ext
  rw [(blkLaws (K := K)).1, neg_zero, zt0, mul_one, mul_one, coe_arc, coe_arc, coe_arc]
  ext r s
  obtain ⟨r, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective r
  obtain ⟨s, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective s
  refine Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace K).injective (C.c.injective (funext fun i => ?_))) ?_
  · rw [ent, u4.1]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact ent C a i r s
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · change C.c (InfiniteAdeleRing.ringEquiv_mixedSpace K 0) i = 0
      rw [map_zero, map_zero]; rfl
    · exact ent C b i r s
  · rw [inf_snd, ← Matrix.submatrix_apply (1 : Matrix _ _ _) finSumFinEquiv finSumFinEquiv, Matrix.submatrix_one_equiv,
      ← Matrix.fromBlocks_one]
    simp only [blk, reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
    rcases r with r | r <;> rcases s with s | s
    · exact inf_snd _ r s
    · rfl
    · rfl
    · exact inf_snd _ r s

private theorem cmm {n : ℕ} (g : archGroup K n) (h : FA K n) : Commute (archP K n g) (fin1 h) :=
  (MultiplicityOne.finProj_mul_archProj_comm h g).symm

private theorem dec (n : ℕ) (k : G1 K n) (hk : k ∈ KG K n) :
    ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  have hk' : (k : AdelicGLn.AdelicGL K n) ∈ Reduction.maxCompact := hk
  have e := infEmb_infPart_mul_finEmb_finPart (k : AdelicGLn.AdelicGL K n)
  have hf : finEmb K n (finPart K n k) ∈ Reduction.maxCompact := by
    refine ⟨fun w => ?_, fun v => ?_⟩
    · have : infAt w (finEmb K n (finPart K n k)) = 1 := by
        refine Units.ext (Matrix.ext fun a b => ?_)
        change (finEmb K n (finPart K n k) a b).1 w = _
        rw [← AdelicGLn.prodEquiv_apply_fst, prodEquiv_finEmb]
        by_cases h : a = b
        · subst h; simp; rfl
        · simp [h]; rfl
      rw [this]; exact one_mem _
    · have : finAt v (finEmb K n (finPart K n k)) = finAt v (k : AdelicGLn.AdelicGL K n) := by
        exact Units.ext (Matrix.ext fun a b => rfl)
      rw [this]; exact hk'.2 v
  refine ⟨⟨infPart K n k, ?_⟩, finPart K n k, (AdelicGLn.mem_integralFiniteGL_iff_forall K n).2 fun v => ?_, Subtype.ext ?_⟩
  · change infEmb K n (infPart K n k) ∈ Reduction.maxCompact
    rw [eq_mul_inv_of_mul_eq e]
    exact mul_mem hk' (inv_mem hf)
  · have : (AdelicGLn.finiteRestrictedEquiv K n (finPart K n k) v : GL (Fin n) (v.adicCompletion K)) =
        finAt v (k : AdelicGLn.AdelicGL K n) := by
      exact Units.ext (Matrix.ext fun a b => rfl)
    rw [this]; exact hk'.2 v
  · rw [Subgroup.coe_mul, coe_arc, fin1, MultiplicityOne.finProj_of_mem (maxCompact_le_normOneGL hf)]
    exact e.symm

private noncomputable def GG (C : Co K ι) : (ι → GL (Fin 2) ℂ) →* G1 K 2 := (archP K 2).comp (C.Ψ 2).symm.toMonoidHom

omit [Fintype ι] in
private theorem gl_eq (C : Co K ι) (i : ι) (a : GL (Fin 2) ℂ) : C.gl i a = GG C (Pi.mulSingle i a) := rfl

omit [Fintype ι] in
private theorem GG_eq (C : Co K ι) (g : archGroup K 2) : archP K 2 g = GG C (C.Ψ 2 g) :=
  congrArg (archP K 2) ((C.Ψ 2).symm_apply_apply g).symm

omit [Fintype ι] in
private theorem GG_cmm (C : Co K ι) (x : ι → GL (Fin 2) ℂ) (h : FA K 2) : Commute (GG C x) (fin1 h) := cmm _ h

omit [Fintype ι] in
private theorem ms_cont (i : ι) : Continuous fun m : GL (Fin 2) ℂ => (Pi.mulSingle i m : ι → GL (Fin 2) ℂ) :=
  continuous_pi fun j => by
    by_cases h : j = i
    · subst h; simpa using continuous_id'
    · simpa [h] using continuous_const

omit [Fintype ι] in
private theorem spl (C : Co K ι) (i : ι) (g : G1 K 2) : ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b) := by
  obtain ⟨A, u, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj g
  obtain ⟨x, hx⟩ : ∃ x, archProj K 2 A = GG C x := ⟨_, GG_eq C ⟨A, Subgroup.mem_top _⟩⟩
  refine ⟨x i, GG C (Function.update x i 1) * fin1 u, ?_, fun b => Commute.mul_left ?_ ?_⟩
  · have : Pi.mulSingle i (x i) * Function.update x i 1 = x := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [gl_eq, ← mul_assoc, ← map_mul, this, hx]
  · rw [gl_eq]
    refine Commute.map ?_ (GG C)
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [gl_eq]
    exact (GG_cmm C _ u).symm

omit [Fintype ι] in
private theorem lst (C : Co K ι) (g : archGroup K 2) :
    ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod := by
  refine ⟨C.Ψ 2 g, fun l hl hm => ?_⟩
  rw [GG_eq C]
  generalize C.Ψ 2 g = x
  have : (l.map fun i => (Pi.mulSingle i (x i) : ι → GL (Fin 2) ℂ)).prod = x := by
    funext j
    rw [Pi.list_prod_apply, List.map_map, List.prod_map_eq_pow_single j, List.count_eq_one_of_mem hl (hm j)]
    · simp
    · intro i hi _
      simp [hi.symm]
  conv_lhs => rw [← this, map_list_prod, List.map_map]
  rfl

omit [Fintype ι] in
private theorem un_eq (C : Co K ι) (i : ι) (m : U2) : C.un i m = C.gl i (kC m) := by
  refine congrArg (archP K 2) ((C.Ψ 2).injective (funext fun j => Units.ext ?_))
  rw [← C.Φ_val, ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.coLaws :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (ι : Type) [Fintype ι] (C : Co K ι), IsHaarK C.κ₂ ∧ (∀ μ, Haar4 μ → IsHaarK (C.κ₄ μ)) ∧ (∀ i m, C.un i m = C.gl i (kC m)) ∧ (∀ i, Continuous (C.gl i)) ∧
      (∀ i a b, C.gl i (a * b) = C.gl i a * C.gl i b) ∧ (∀ i j, i ≠ j → ∀ a b, Commute (C.gl i a) (C.gl j b)) ∧
      (∀ i a (h : FA K 2), Commute (C.gl i a) (fin1 h)) ∧ (∀ i (g : G1 K 2), ∃ a h, g = C.gl i a * h ∧ ∀ b, Commute h (C.gl i b)) ∧
      (∀ g : archGroup K 2, ∃ a : ι → GL (Fin 2) ℂ, ∀ l : List ι, l.Nodup → (∀ i, i ∈ l) → archP K 2 g = (l.map fun i => C.gl i (a i)).prod) ∧
      (∀ a b : ι → U2, lv (arc1 ((C.Φ 2).symm a)) (arc1 ((C.Φ 2).symm b)) 0 = arc1 ((C.Φ (2 + 2)).symm fun i => bd (a i) (b i))) ∧
      (∀ n (k : archCompact K n) (h : FA K n), Commute (arc1 k) (fin1 h)) ∧
      ∀ n, ∀ k ∈ KG K n, ∃ (a : archCompact K n) (h : FA K n), h ∈ AdelicGLn.integralFiniteGL K n ∧ k = arc1 a * fin1 h := by
  intro K _ _ _ ι _ C
  refine ⟨haar _ _ (measurePreserving_mul_left μK) (measurePreserving_mul_right μK), fun μ hμ => ?_, un_eq C, fun i => ?_,
    fun i a b => ?_, fun i j hij a b => ?_, fun i a h => cmm _ h, spl C, lst C, blkA C, fun n k h => cmm _ h, dec⟩
  · haveI := hμ.prob
    exact haar _ μ hμ.left hμ.right
  · exact continuous_archP.comp ((C.Ψ 2).symm.continuous.comp (ms_cont i))
  · rw [gl_eq, gl_eq, gl_eq, Pi.mulSingle_mul, map_mul]
  · rw [gl_eq, gl_eq]
    exact (Pi.mulSingle_commute (f := fun _ => GL (Fin 2) ℂ) hij a b).map (GG C)
