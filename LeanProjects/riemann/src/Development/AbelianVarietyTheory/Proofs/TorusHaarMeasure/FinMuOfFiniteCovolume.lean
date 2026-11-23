import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

theorem measure_le_of_cover {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Countable ι] (ν : Measure G) [ν.IsMulLeftInvariant] (ρ : ι → G) {T Ω : Set G}
    (hT : MeasurableSet T) (hΩ : MeasurableSet Ω) (hcov : ∀ g, ∃ i, ∃ w ∈ Ω, g = ρ i * w)
    (huniq : ∀ w i j, ρ i * w ∈ T → ρ j * w ∈ T → i = j) : ν T ≤ ν Ω := by
  classical
  have hS : ∀ i, MeasurableSet (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := fun i =>
    hΩ.inter (measurable_const_mul (ρ i) hT)
  have hdisj : Pairwise (Function.onFun Disjoint fun i => Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro w ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (huniq w i j hi hj)
  have hsub : T ⊆ ⋃ i, (fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
    intro g hg
    obtain ⟨i, w, hw, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨i, w, ⟨hw, hg⟩, rfl⟩
  calc ν T ≤ ν (⋃ i, (fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T)) := measure_mono hsub
    _ ≤ ∑' i, ν ((fun w => ρ i * w) '' (Ω ∩ (fun w => ρ i * w) ⁻¹' T)) := measure_iUnion_le _
    _ = ∑' i, ν (Ω ∩ (fun w => ρ i * w) ⁻¹' T) := by
        congr 1
        funext i
        rw [Set.image_mul_left, measure_preimage_mul]
    _ = ν (⋃ i, Ω ∩ (fun w => ρ i * w) ⁻¹' T) := (measure_iUnion hdisj hS).symm
    _ ≤ ν Ω := measure_mono (Set.iUnion_subset fun _ => Set.inter_subset_left)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isUStab_inv {r : ℕ} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    {γ : GL (Fin r) E} (h : IsUStab G Λ γ) : IsUStab G Λ γ⁻¹ := by
  have key : ∀ v : Fin r → E, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E)
      (Matrix.mulVec ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← h.1, key, key]
  · have hx := h.2 (Matrix.mulVec ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) x)
    rw [key] at hx
    exact hx.symm

noncomputable def embGL {r : ℕ} (Ψ : Finset (E →+* ℂ)) : GL (Fin r) E →* (Ψ → GL (Fin r) ℂ) :=
  Pi.monoidHom fun τ : Ψ => Matrix.GeneralLinearGroup.map τ.1

omit [NumberField E] [IsCMField E] in
theorem embGL_val {r : ℕ} (Ψ : Finset (E →+* ℂ)) (γ : GL (Fin r) E) (τ : Ψ) :
    ((embGL Ψ γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 := rfl

omit [NumberField E] [IsCMField E] in
theorem hermC_eq_dotProduct {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v : Fin r → ℂ) :
    hermC τ G u v = u ⬝ᵥ (G.map τ *ᵥ (starRingEnd ℂ ∘ v)) := by
  unfold hermC
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Function.comp_apply, Finset.mul_sum, mul_assoc]

private theorem transpose_mul_mul_map_eq_of_isUStab {r : ℕ} {G : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
    {γ : GL (Fin r) E} (h : IsUStab G Λ γ) :
    (γ : Matrix (Fin r) (Fin r) E)ᵀ * G * (γ : Matrix (Fin r) (Fin r) E).map cc = G := by
  ext i j
  have h1 := h.1 (Pi.single i 1) (Pi.single j 1)
  simp only [herm, Matrix.mulVec_single_one] at h1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  convert h1 using 1
  all_goals simp [Pi.single_apply, cc, apply_ite]

theorem isUnitaryC_of_isUStab {r : ℕ} (X : Data E r) {γ : GL (Fin r) E} (hγ : IsUStab X.Gm X.Λ γ) :
    X.IsUnitaryC fun τ => ((embGL X.Ψ γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  intro τ u w
  have hbar : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) =
      ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 := by
    ext a b
    simp [cc, NumberField.IsCMField.complexEmbedding_complexConj]
  have hG : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * (X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ)) = X.Gm.map τ.1 := by
    rw [hbar, ← Matrix.mul_assoc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      transpose_mul_mul_map_eq_of_isUStab hγ]
  have hconj : (starRingEnd ℂ) ∘ Matrix.mulVec ((γ : Matrix (Fin r) (Fin r) E).map τ.1) w =
      Matrix.mulVec (((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ))
        ((starRingEnd ℂ) ∘ w) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  beta_reduce
  rw [hermC_eq_dotProduct, hermC_eq_dotProduct, embGL_val, hconj, Matrix.mulVec_mulVec,
    ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hG]

def cellOver {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (FF ×ˢ Bor X.Ψ r)

omit [NumberField E] [IsCMField E] in
theorem measurableSet_Bor {r : ℕ} (Ψ : Finset (E →+* ℂ)) : MeasurableSet (Bor Ψ r) := by
  have hset : Bor Ψ r = ⋂ τ : Ψ, ((fun b : Frame Ψ r => (mat b τ).det) ⁻¹' {0}ᶜ ∩
      ⋂ a : Fin r, ⋂ c : Fin r, {b : Frame Ψ r | c < a → b τ a c = 0}) := by
    ext b
    simp [Bor]
  rw [hset]
  refine MeasurableSet.iInter fun τ => ?_
  refine MeasurableSet.inter ?_ (MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => ?_)
  · have hc : Continuous fun b : Frame Ψ r => (mat b τ).det :=
      Continuous.matrix_det (continuous_apply τ)
    exact hc.measurable (measurableSet_singleton 0).compl
  · by_cases hca : c < a
    · simp only [hca, true_implies]
      exact (measurableSet_singleton (0 : ℂ)).preimage
        (by fun_prop : Measurable fun b : Frame Ψ r => b τ a c)
    · simp [hca]

private theorem mat_rmul' {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x b : Frame Ψ r) (τ : Ψ) :
    mat (rmul x b) τ = mat x τ * mat b τ := by rfl

private theorem mat_lact' {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ : GL (Fin r) K) (x : Frame Ψ r) (τ : Ψ) :
    mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) K).map τ.1 * mat x τ := by rfl

private theorem frame_ext_of_mat_eq {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {x y : Frame Ψ r}
    (h : ∀ τ, mat x τ = mat y τ) : x = y :=
  funext fun τ => h τ

private theorem rmul_rmul_eq_rmul_rmul {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x b c : Frame Ψ r) :
    rmul (rmul x b) c = rmul x (rmul b c) :=
  frame_ext_of_mat_eq fun τ => by simp only [mat_rmul', Matrix.mul_assoc]

private theorem blockTriangular_mat_of_mem_bor {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) (τ : Ψ) :
    (mat b τ).BlockTriangular id := by
  intro i j h
  exact (hb τ).2 i j h

private theorem exists_bor_right_identity {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} :
    ∃ o : Frame Ψ r, o ∈ Bor Ψ r ∧ ∀ x : Frame Ψ r, rmul x o = x := by
  refine ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c h => ?_⟩,
    fun x => frame_ext_of_mat_eq fun τ => ?_⟩
  · show (1 : Matrix (Fin r) (Fin r) ℂ).det ≠ 0
    simp
  · exact Matrix.one_apply_ne h.ne'
  · exact Matrix.mul_one (mat x τ)

private theorem rmul_mem_Bor {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : c ∈ Bor Ψ r) : rmul b c ∈ Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a d h => ?_⟩
  · rw [mat_rmul', Matrix.det_mul]
    exact mul_ne_zero (hb τ).1 (hc τ).1
  · exact ((blockTriangular_mat_of_mem_bor hb τ).mul (blockTriangular_mat_of_mem_bor hc τ)) h

private theorem exists_bor_right_inverse {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) :
    ∃ c : Frame Ψ r, c ∈ Bor Ψ r ∧ ∀ x : Frame Ψ r, rmul (rmul x b) c = x := by
  refine ⟨fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ), fun τ => ?_,
    fun x => frame_ext_of_mat_eq fun τ => ?_⟩
  · have hu : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
    let _ := Matrix.invertibleOfIsUnitDet _ hu
    refine ⟨(Matrix.isUnit_nonsing_inv_det _ hu).ne_zero, fun a c h => ?_⟩
    exact (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_of_mem_bor hb τ)) h
  · show mat x τ * mat b τ * (mat b τ)⁻¹ = mat x τ
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hb τ).1), Matrix.mul_one]

private theorem gram_eq_lemma {K : Type} [Field K] {r : ℕ} (τ : K →+* ℂ) (G : Matrix (Fin r) (Fin r) K)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private theorem det_mat_ne_zero_of_isOrth_frame {r : ℕ} {X : Data E r} {x : Frame X.Ψ r} (hx : IsOrth X x)
    (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro hdet
  have h := congrArg Matrix.det (hx τ)
  rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, zero_mul, zero_mul,
    Matrix.det_diagonal] at h
  refine (Finset.prod_ne_zero_iff.2 fun i _ => ?_) h.symm
  unfold sgn
  split_ifs <;> norm_num

private theorem mat_nmat_diag_eq_one {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    mat (nmat X z) τ a a = 1 := by
  simp [mat, nmat]

private theorem blockTriangular_mat_nmat_lower {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
  intro a c h
  have h' : a < c := OrderDual.toDual_lt_toDual.1 h
  simp [mat, nmat, not_lt.2 h'.le, h'.ne]

private theorem det_mat_nmat_eq_one {r : ℕ} (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (blockTriangular_mat_nmat_lower X z τ)]
  simp [mat_nmat_diag_eq_one]

private theorem eq_of_mat_nmat_eq {r : ℕ} (X : Data E r) {z z' : V (nd X)}
    (h : ∀ τ, mat (nmat X z) τ = mat (nmat X z') τ) : z = z' := by
  ext k
  rcases he : (Fintype.equivFin (Ent X)).symm k with ⟨τ, ⟨⟨a, c⟩, hac⟩⟩
  have h1 := congrFun (congrFun (h τ) a) c
  have hk : k = Fintype.equivFin (Ent X) ⟨τ, ⟨(a, c), hac⟩⟩ := by
    rw [← he]
    exact ((Fintype.equivFin (Ent X)).apply_symm_apply k).symm
  simp only [mat, nmat, Matrix.of_apply, dif_pos hac] at h1
  rw [hk]
  exact h1

private theorem eq_of_rmul_cpt_eq_rmul_cpt {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {z z' : V (nd X)} {b b' : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r)
    (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') : z = z' ∧ b = b' := by
  have hN : ∀ τ, mat (nmat X z) τ = mat (nmat X z') τ := by
    intro τ
    have h1 := congrArg (fun y => mat y τ) h
    simp only [cpt, mat_rmul', Matrix.mul_assoc] at h1
    have hu0 : IsUnit (mat x0 τ) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (det_mat_ne_zero_of_isOrth_frame ho τ))
    have h2 := hu0.mul_left_cancel h1
    have huN' : IsUnit (mat (nmat X z') τ).det := by
      rw [det_mat_nmat_eq_one]
      exact isUnit_one
    have huB : IsUnit (mat b τ).det := isUnit_iff_ne_zero.2 (hb τ).1
    have hD : (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ = mat b' τ * (mat b τ)⁻¹ := by
      calc (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ
          = (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ * (mat b τ * (mat b τ)⁻¹) := by
            rw [Matrix.mul_nonsing_inv _ huB, Matrix.mul_one]
        _ = (mat (nmat X z') τ)⁻¹ * (mat (nmat X z) τ * mat b τ) * (mat b τ)⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = (mat (nmat X z') τ)⁻¹ * (mat (nmat X z') τ * mat b' τ) * (mat b τ)⁻¹ := by rw [h2]
        _ = mat b' τ * (mat b τ)⁻¹ := by
            rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ huN', Matrix.one_mul]
    have hlow : ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ).BlockTriangular OrderDual.toDual := by
      let _ := Matrix.invertibleOfIsUnitDet _ huN'
      exact (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_nmat_lower X z' τ)).mul
        (blockTriangular_mat_nmat_lower X z τ)
    have hup : (mat b' τ * (mat b τ)⁻¹).BlockTriangular id := by
      let _ := Matrix.invertibleOfIsUnitDet _ huB
      exact (blockTriangular_mat_of_mem_bor hb' τ).mul (Matrix.blockTriangular_inv_of_blockTriangular (blockTriangular_mat_of_mem_bor hb τ))
    have hoff : ∀ i j, i ≠ j → ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ) i j = 0 := by
      intro i j hij
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · exact hlow (OrderDual.toDual_lt_toDual.2 hlt)
      · rw [hD]
        exact hup hlt
    have hNeq : mat (nmat X z) τ =
        mat (nmat X z') τ * ((mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ) := by
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huN', Matrix.one_mul]
    have hone : (mat (nmat X z') τ)⁻¹ * mat (nmat X z) τ = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        have h3 := congrFun (congrFun hNeq i) i
        rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff k i hki, mul_zero])
          (by simp), mat_nmat_diag_eq_one, mat_nmat_diag_eq_one, one_mul] at h3
        rw [Matrix.one_apply_eq]
        exact h3.symm
      · rw [hoff i j hij, Matrix.one_apply_ne hij]
    rw [hNeq, hone, Matrix.mul_one]
  have hz := eq_of_mat_nmat_eq X hN
  subst hz
  refine ⟨rfl, frame_ext_of_mat_eq fun τ => ?_⟩
  have h1 := congrArg (fun y => mat y τ) h
  simp only [mat_rmul'] at h1
  have hu : IsUnit (mat (cpt X x0 z) τ) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 ?_)
    rw [cpt, mat_rmul', Matrix.det_mul, det_mat_nmat_eq_one, mul_one]
    exact det_mat_ne_zero_of_isOrth_frame ho τ
  exact hu.mul_left_cancel h1

private theorem continuous_dmin' {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) :
    Continuous fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2 := by
  have hn : Continuous fun z : V (nd X) => nmat X z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
    simp only [nmat]
    split_ifs
    · exact PiLp.continuous_apply _ _ _
    · exact continuous_const
    · exact continuous_const
  refine continuous_pi fun τ => ?_
  show Continuous fun p : V (nd X) × Frame X.Ψ r => mat x0 τ * mat (nmat X p.1) τ * mat p.2 τ
  exact (continuous_const.matrix_mul ((continuous_apply τ).comp (hn.comp continuous_fst))).matrix_mul
    ((continuous_apply τ).comp continuous_snd)

theorem measurableSet_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} (hm : MeasurableSet FF) (hO : FF ⊆ OmF X x0) :
    MeasurableSet (cellOver X x0 FF) := by
  have : TopologicalSpace.IsCompletelyMetrizableSpace (Fin r → Fin r → ℂ) := inferInstance
  have : TopologicalSpace.IsCompletelyMetrizableSpace (Frame X.Ψ r) := inferInstance
  have : TopologicalSpace.SeparableSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X)) := inferInstance
  have : PolishSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X) × Frame X.Ψ r) := inferInstance

  unfold cellOver
  refine MeasurableSet.image_of_continuousOn_injOn (hm.prod (measurableSet_Bor X.Ψ))
    (continuous_dmin' X x0).continuousOn ?_
  rintro ⟨z, b⟩ ⟨_, hb⟩ ⟨z', b'⟩ ⟨_, hb'⟩ h
  obtain ⟨rfl, rfl⟩ := eq_of_rmul_cpt_eq_rmul_cpt X ho hb hb' h
  rfl

theorem rmul_mem_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    {x b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ cellOver X x0 FF ↔ x ∈ cellOver X x0 FF := by
  constructor
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, hx⟩
    dsimp only at hx
    obtain ⟨binv, hbinv, hcancel⟩ := exists_bor_right_inverse hb
    refine ⟨(z, rmul c binv), ⟨hz, rmul_mem_Bor hc hbinv⟩, ?_⟩
    show rmul (cpt X x0 z) (rmul c binv) = x
    rw [← rmul_rmul_eq_rmul_rmul, hx, hcancel]
  · rintro ⟨⟨z, c⟩, ⟨hz, hc⟩, hx⟩
    dsimp only at hx
    refine ⟨(z, rmul c b), ⟨hz, rmul_mem_Bor hc hb⟩, ?_⟩
    show rmul (cpt X x0 z) (rmul c b) = rmul x b
    rw [← rmul_rmul_eq_rmul_rmul, hx]

theorem cpt_mem_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {FF : Set (V (nd X))} {z : V (nd X)} : cpt X x0 z ∈ cellOver X x0 FF ↔ z ∈ FF := by
  obtain ⟨o, ho1, ho2⟩ := exists_bor_right_identity (Ψ := X.Ψ) (r := r)
  constructor
  · rintro ⟨⟨z', c⟩, ⟨hz', hc⟩, hx⟩
    dsimp only at hx
    have hzz := eq_of_rmul_cpt_eq_rmul_cpt X ho hc ho1 (hx.trans (ho2 _).symm)
    exact hzz.1 ▸ hz'
  · intro hz
    exact ⟨(z, o), ⟨hz, ho1⟩, ho2 _⟩

private theorem lact_mul_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ γ' : GL (Fin r) K) (x : Frame Ψ r) :
    lact (γ * γ') x = lact γ (lact γ' x) :=
  frame_ext_of_mat_eq fun τ => by
    simp only [mat_lact', Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private theorem lact_one_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (x : Frame Ψ r) : lact 1 x = x :=
  frame_ext_of_mat_eq fun τ => by
    rw [mat_lact', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

private theorem lact_rmul_torus_haar_measure {K : Type} [Field K] {Ψ : Finset (K →+* ℂ)} {r : ℕ} (γ : GL (Fin r) K) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b :=
  frame_ext_of_mat_eq fun τ => by
    simp only [mat_lact', mat_rmul', Matrix.mul_assoc]

theorem eq_of_lact_mem_cellOver {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {δ δ' : GL (Fin r) E} (hδ : δ ∈ X.Γ) (hδ' : δ' ∈ X.Γ)
    (h : lact δ x ∈ cellOver X x0 FF) (h' : lact δ' x ∈ cellOver X x0 FF) : δ = δ' := by
  obtain ⟨⟨z, c⟩, ⟨hz, hc⟩, hx⟩ := h
  obtain ⟨⟨z', c'⟩, ⟨hz', hc'⟩, hx'⟩ := h'
  dsimp only at hx hx'
  obtain ⟨cinv, hcinv, hcc⟩ := exists_bor_right_inverse hc'
  have hγ : δ' * δ⁻¹ ∈ X.Γ := X.Γ.mul_mem hδ' (X.Γ.inv_mem hδ)
  have hbb : rmul c cinv ∈ Bor X.Ψ r := rmul_mem_Bor hc hcinv
  have hkey : cpt X x0 z' = lact (δ' * δ⁻¹) (rmul (cpt X x0 z) (rmul c cinv)) := by
    rw [← rmul_rmul_eq_rmul_rmul, hx, lact_rmul_torus_haar_measure, ← lact_mul_torus_haar_measure, inv_mul_cancel_right, ← hx', hcc]
  have hzz : z = z' := hFF.2.2.1 z hz z' hz' _ hγ _ hbb hkey
  rw [← hzz] at hkey
  have hdom : cpt X x0 z ∈ X.dom := hFF.2.1 hz
  have h1 : lact (δ' * δ⁻¹)⁻¹ (cpt X x0 z) = rmul (cpt X x0 z) (rmul c cinv) := by
    conv_lhs => rw [hkey]
    rw [← lact_mul_torus_haar_measure, inv_mul_cancel, lact_one_torus_haar_measure]
  have h2 := X.Γ_free _ (X.Γ.inv_mem hγ) _ hdom _ hbb h1
  rw [inv_eq_one, mul_inv_eq_one] at h2
  exact h2.symm

private theorem isUStab_mul' {r : ℕ} {G : Matrix (Fin r) (Fin r) E}
    {Λ : Submodule (𝓞 E) (Fin r → E)} {γ γ' : GL (Fin r) E} (h1 : IsUStab G Λ γ)
    (h2 : IsUStab G Λ γ') : IsUStab G Λ (γ * γ') := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1.1, h2.1]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (h2.2 x).trans (h1.2 _)

theorem finMu_of_finite_covolume :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ((∀ (r : ℕ) (X : Data E r), ∃ H : Subgroup (X.Ψ → GL (Fin r) ℂ), ∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) ∧ (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → LocallyCompactSpace H ∧ SecondCountableTopology H ∧ ∀ x0, IsOrth X x0 → (∀ g : H, IsOrth X (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) ∧ ∃ ι : Frame X.Ψ r → H, ContinuousOn ι {x | IsOrth X x} ∧ (∀ x, IsOrth X x → X.lmulC (fun τ => ((ι x : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0 = x) ∧ ∀ g : H, ι (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = g)) → (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ ν : Measure H, ν.IsMulLeftInvariant ∧ IsFiniteMeasureOnCompacts ν ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) → ∫⁻ g, φ (X.lmulC (fun τ => ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) ∂ν = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0) → (∀ (r : ℕ) (X : Data E r), PropDisc X) → (∀ (r : ℕ) (X : Data E r), FinMu X) := by
  intro hA hB hC hD r X
  classical
  obtain ⟨H, hH⟩ := hB.1 r X
  obtain ⟨hLC, hSC, -⟩ := hB.2 r X H hH
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hfs : FundSetStatement (E := E) := fundSet_holds
  obtain ⟨FF, hFF⟩ := hfs r X (x0F X) hx0 (hD r X)

  obtain ⟨ν, hνinv, hνfin, hνint⟩ := hC r X H hH (x0F X) hx0
  have := hνinv
  have := hνfin
  refine ⟨x0F X, hx0, FF, hFF, ?_⟩
  have : LocallyCompactSpace H := hLC
  have : SecondCountableTopology H := hSC
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  have : Countable (GL (Fin r) E) := Units.val_injective.countable
  obtain ⟨Ω, hΩm, hΩfin, hΩcov⟩ := hA r X H hH (MeasureTheory.Measure.haar)
  have hcell : MeasurableSet (cellOver X (x0F X) FF) :=
    measurableSet_cellOver X hx0 hFF.1 hFF.2.1
  have hfc : Continuous fun g : H =>
      X.lmulC (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        (x0F X) := by
    refine continuous_pi fun τ => ?_
    show Continuous fun g : H =>
      (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat (x0F X) τ
    exact (Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)).matrix_mul
      continuous_const
  have hT : MeasurableSet ((fun g : H =>
      X.lmulC (fun τ => (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ))
        (x0F X)) ⁻¹' cellOver X (x0F X) FF) := hfc.measurable hcell
  have hφ := hνint ((cellOver X (x0F X) FF).indicator 1) (measurable_one.indicator hcell)
    (fun x _ b hb => by simp only [Set.indicator_apply, rmul_mem_cellOver X hb, Pi.one_apply])
  clear hA hB hC hD hfs hνint
  have hR : ∫⁻ z, (cellOver X (x0F X) FF).indicator 1 (cpt X (x0F X) z) ∂muF X (x0F X) =
      muF X (x0F X) FF := by
    rw [← lintegral_indicator_one hFF.1]
    congr 1
    funext z
    simp only [Set.indicator_apply, cpt_mem_cellOver X hx0, Pi.one_apply]
  have hL : ∫⁻ g, (cellOver X (x0F X) FF).indicator 1 (X.lmulC (fun τ =>
      (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) (x0F X)) ∂ν =
      ν ((fun g : H => X.lmulC (fun τ =>
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) (x0F X)) ⁻¹'
          cellOver X (x0F X) FF) := by
    rw [← lintegral_indicator_one hT]
    congr 1

  let ρ : X.Γ → H := fun δ => ⟨embGL X.Ψ δ.1, (hH _).2 (isUnitaryC_of_isUStab X (X.Γ_stab _ δ.2))⟩
  have hρ : ∀ δ : X.Γ, ((ρ δ : H) : X.Ψ → GL (Fin r) ℂ) = embGL X.Ψ δ.1 := fun δ => rfl

  obtain ⟨S, hS⟩ := X.Γ_index
  let σ : GL (Fin r) E → H := fun s => if hs : IsUStab X.Gm X.Λ s⁻¹ then
    ⟨embGL X.Ψ s⁻¹, (hH _).2 (isUnitaryC_of_isUStab X hs)⟩ else 1
  have hνΩ : ν Ω < ⊤ := by
    rw [MeasureTheory.Measure.isMulLeftInvariant_eq_smul ν MeasureTheory.Measure.haar,
      MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hΩfin
  have hΩ'm : MeasurableSet (⋃ s ∈ S, (fun w => σ s * w) '' Ω) := by
    refine Finset.measurableSet_biUnion S fun s _ => ?_
    rw [Set.image_mul_left]
    exact measurable_const_mul _ hΩm
  have hcov : ∀ g : H, ∃ i : X.Γ, ∃ w ∈ ⋃ s ∈ S, (fun w => σ s * w) '' Ω, g = ρ i * w := by
    intro g
    obtain ⟨γ, hγ, w, hw, hgw⟩ := hΩcov g
    obtain ⟨s, hsS, hsΓ⟩ := hS γ⁻¹ (isUStab_inv hγ)
    have hδ : γ * s ∈ X.Γ := by
      have := X.Γ.inv_mem hsΓ
      rwa [mul_inv_rev, inv_inv, inv_inv] at this
    have hsu : IsUStab X.Gm X.Λ s⁻¹ := by
      have he : s⁻¹ = (γ * s)⁻¹ * γ := by group
      rw [he]
      exact isUStab_mul' (X.Γ_stab _ (X.Γ.inv_mem hδ)) hγ
    refine ⟨⟨γ * s, hδ⟩, σ s * w, Set.mem_iUnion₂.2 ⟨s, hsS, w, hw, rfl⟩, ?_⟩
    have hσ : ((σ s : H) : X.Ψ → GL (Fin r) ℂ) = embGL X.Ψ s⁻¹ := by
      simp only [σ, dif_pos hsu]
    apply Subtype.ext
    funext τ
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Pi.mul_apply, Pi.mul_apply, Units.val_mul, Units.val_mul, hσ,
      hρ, embGL_val, embGL_val, hgw τ, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul,
      mul_inv_cancel_right]
  have hfmul : ∀ (i : X.Γ) (w : H),
      X.lmulC (fun τ => ((((ρ i * w : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ)) (x0F X) =
      lact i.1 (X.lmulC (fun τ => (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) :
        Matrix (Fin r) (Fin r) ℂ)) (x0F X)) := by
    intro i w
    refine frame_ext_of_mat_eq fun τ => ?_
    rw [mat_lact']
    show ((((ρ i * w : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) *
        mat (x0F X) τ = (i.1 : Matrix (Fin r) (Fin r) E).map τ.1 *
        ((((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat (x0F X) τ)
    rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hρ, embGL_val, Matrix.mul_assoc]
  have huniq : ∀ (w : H) (i j : X.Γ),
      ρ i * w ∈ (fun g : H => X.lmulC (fun τ =>
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) (x0F X)) ⁻¹'
          cellOver X (x0F X) FF →
      ρ j * w ∈ (fun g : H => X.lmulC (fun τ =>
        (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) (x0F X)) ⁻¹'
          cellOver X (x0F X) FF → i = j := by
    intro w i j hi hj
    rw [Set.mem_preimage, hfmul] at hi hj
    exact Subtype.ext (eq_of_lact_mem_cellOver X hFF i.2 j.2 hi hj)
  calc muF X (x0F X) FF
      = ∫⁻ z, (cellOver X (x0F X) FF).indicator 1 (cpt X (x0F X) z) ∂muF X (x0F X) := hR.symm
    _ = _ := hφ.symm
    _ = _ := hL
    _ ≤ ν (⋃ s ∈ S, (fun w => σ s * w) '' Ω) := measure_le_of_cover ν ρ hT hΩ'm hcov huniq
    _ ≤ ∑ s ∈ S, ν ((fun w => σ s * w) '' Ω) := measure_biUnion_finset_le S _
    _ = ∑ s ∈ S, ν Ω := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Set.image_mul_left, measure_preimage_mul]
    _ < ⊤ := ENNReal.sum_lt_top.2 fun s _ => hνΩ

end GlobalTheory.FiniteCovolume
