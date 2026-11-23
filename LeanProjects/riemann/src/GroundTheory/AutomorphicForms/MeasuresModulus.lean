import Mathlib
import GroundTheory.AutomorphicForms.GLnLocal

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

section Topology

theorem countable_units_valueGroup : Countable (ValueGroupWithZero F)ˣ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero F)ˣ)
  refine Function.Surjective.countable (f := fun k : ℤ => g ^ k) fun x => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  exact ⟨k, hk⟩

theorem metrizableSpace : TopologicalSpace.MetrizableSpace F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  have := countable_units_valueGroup F
  have : (𝓝 (0 : F)).IsCountablyGenerated :=
    (IsValuativeTopology.hasBasis_nhds_zero F).isCountablyGenerated
  have : (uniformity F).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero F]
    infer_instance
  exact UniformSpace.metrizableSpace

theorem sigmaCompactSpace : SigmaCompactSpace F := by
  refine ⟨⟨fun k : ℕ => {x | valuation F x ≤ (valuation F (GLnLocal.uniformizer F : F))⁻¹ ^ k},
    fun k => IsNonarchimedeanLocalField.isCompact_closedBall F _, ?_⟩⟩
  refine Set.eq_univ_of_forall fun x => ?_
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (GLnLocal.valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have hϖ := GLnLocal.valuation_uniformizer_ne_zero F
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m * valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  have hm0 : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0 := pow_ne_zero _ hϖ
  rw [inv_pow, ← mul_one ((valuation F (GLnLocal.uniformizer F : F) ^ m)⁻¹),
    le_inv_mul_iff₀ (zero_lt_iff.mpr hm0)]
  exact h1.le

instance secondCountableTopology : SecondCountableTopology F := by
  have := metrizableSpace F
  have := sigmaCompactSpace F
  let := TopologicalSpace.metrizableSpaceMetric F
  exact EMetric.secondCountable_of_sigmaCompact F

theorem secondCountableTopology_units {M : Type*} [Monoid M] [TopologicalSpace M]
    [SecondCountableTopology M] : SecondCountableTopology Mˣ :=
  haveI : SecondCountableTopology Mᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  Units.isEmbedding_embedProduct.secondCountableTopology

instance secondCountableTopology_GL (ι : Type*) [Fintype ι] [DecidableEq ι] :
    SecondCountableTopology (GL ι F) :=
  haveI : SecondCountableTopology (Matrix ι ι F) :=
    inferInstanceAs (SecondCountableTopology (ι → ι → F))
  secondCountableTopology_units

end Topology

section Modulus

variable {F} {ι : Type*} [Fintype ι]

instance continuousConstSMul_linearEquiv :
    ContinuousConstSMul ((ι → F) ≃ₗ[F] (ι → F)) (ι → F) :=
  ⟨fun L => (L.toLinearMap).continuous_on_pi⟩

variable (F ι) in

def box : Set (ι → F) := Set.univ.pi fun _ => (𝒪[F] : Set F)

theorem mem_box {x : ι → F} : x ∈ box F ι ↔ ∀ i, x i ∈ 𝒪[F] := by
  simp [box]

theorem isOpen_box : IsOpen (box F ι) :=
  isOpen_set_pi Set.finite_univ fun _ _ => Valuation.isOpen_integer

theorem isCompact_box : IsCompact (box F ι) :=
  isCompact_univ_pi fun _ => isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace 𝒪[F]))

theorem zero_mem_box : (0 : ι → F) ∈ box F ι := fun _ _ => (𝒪[F]).zero_mem

theorem distribHaarChar_eq_one_of_image_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h : L '' box F ι = box F ι) : distribHaarChar (ι → F) L = 1 := by
  borelize (ι → F)
  let μ : Measure (ι → F) := Measure.addHaar
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  have : L • box F ι = L '' box F ι := rfl
  rw [this, h, ENNReal.coe_one, one_mul]

theorem distribHaarChar_eq_one_of_mapsTo_box {L : (ι → F) ≃ₗ[F] (ι → F)}
    (h₁ : ∀ x ∈ box F ι, L x ∈ box F ι) (h₂ : ∀ x ∈ box F ι, L.symm x ∈ box F ι) :
    distribHaarChar (ι → F) L = 1 := by
  refine distribHaarChar_eq_one_of_image_box (Set.Subset.antisymm ?_ fun x hx => ?_)
  · rintro _ ⟨x, hx, rfl⟩
    exact h₁ x hx
  · exact ⟨L.symm x, h₂ x hx, L.apply_symm_apply x⟩

variable [DecidableEq ι]

theorem mulVec_mem_box {A : Matrix ι ι F} (hA : ∀ i j, A i j ∈ 𝒪[F]) {x : ι → F}
    (hx : x ∈ box F ι) : A.mulVec x ∈ box F ι :=
  mem_box.2 fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (mem_box.1 hx j)

noncomputable def modulus : F →*₀ ℝ≥0 where
  toFun x := by classical exact if h : x = 0 then 0 else distribHaarChar F (Units.mk0 x h)
  map_zero' := dif_pos rfl
  map_one' := by
    rw [dif_neg one_ne_zero]
    convert map_one (distribHaarChar F (G := Fˣ))
    ext
    rfl
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [dif_neg (mul_ne_zero hx hy), dif_neg hx, dif_neg hy, ← map_mul]
    congr 1
    ext
    rfl

theorem modulus_units (u : Fˣ) : modulus (u : F) = distribHaarChar F u := by
  rw [modulus, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, dif_neg u.ne_zero]
  congr 1
  ext
  rfl

theorem modulus_ne_zero {x : F} (hx : x ≠ 0) : modulus x ≠ 0 := by
  rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, modulus_units]
  exact distribHaarChar_pos.ne'

noncomputable def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

theorem glEquiv_apply (g : GL ι F) (x : ι → F) : glEquiv g x = (g : Matrix ι ι F).mulVec x := by
  simp [glEquiv, LinearMap.GeneralLinearGroup.generalLinearEquiv, Matrix.GeneralLinearGroup.toLin]

theorem det_glEquiv (g : GL ι F) :
    LinearEquiv.det (glEquiv g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [LinearEquiv.coe_det]
  show LinearMap.det (Matrix.toLin' (g : Matrix ι ι F)) = _
  rw [LinearMap.det_toLin']
  rfl

theorem distribHaarChar_glEquiv_eq_one {g : GL ι F} (h₁ : ∀ a b, (g : Matrix ι ι F) a b ∈ 𝒪[F])
    (h₂ : ∀ a b, ((g⁻¹ : GL ι F) : Matrix ι ι F) a b ∈ 𝒪[F]) :
    distribHaarChar (ι → F) (glEquiv g) = 1 := by
  refine distribHaarChar_eq_one_of_mapsTo_box (fun x hx => ?_) (fun x hx => ?_)
  · rw [glEquiv_apply]
    exact mulVec_mem_box h₁ hx
  · rw [show (glEquiv g).symm = glEquiv g⁻¹ from (map_inv glEquiv g).symm, glEquiv_apply]
    exact mulVec_mem_box h₂ hx

theorem transvection_mem_integer {i j : ι} {c : F} (hc : c ∈ 𝒪[F]) (a b : ι) :
    Matrix.transvection i j c a b ∈ 𝒪[F] := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine Subring.add_mem _ ?_ ?_
  · split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · split_ifs
    · exact hc
    · exact Subring.zero_mem _

theorem distribHaarChar_glEquiv_diagonal {D : ι → F} (h : (Matrix.diagonal D).det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) =
      distribHaarChar F (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) := by
  have hD : ∀ i, D i ≠ 0 := fun i => by
    rw [Matrix.det_diagonal] at h
    exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
  let u : ι → Fˣ := fun i => Units.mk0 (D i) (hD i)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) =
      ∏ i, u i := by
    ext
    simp [u, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_diagonal]
  rw [hdet, map_prod]
  borelize F
  let ν : Measure F := Measure.addHaar
  let μ : Measure (ι → F) := Measure.pi fun _ => ν
  have himage : glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) • box F ι =
      Set.univ.pi fun i => u i • (𝒪[F] : Set F) := by
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨y, hy, rfl⟩ i
      refine ⟨y i, mem_box.1 hy i, ?_⟩
      simp [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal]
    · intro hx
      choose y hy hyx using hx
      refine ⟨y, mem_box.2 hy, funext fun i => ?_⟩
      simpa [LinearEquiv.smul_def, glEquiv_apply, u, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mulVec_diagonal, Units.smul_def] using hyx i
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := box F ι)
    (isOpen_box.measure_ne_zero μ ⟨0, zero_mem_box⟩) isCompact_box.measure_lt_top.ne ?_
  rw [himage, box, Measure.pi_pi, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (distribHaarChar_mul ν (u i) _).symm

theorem distribHaarChar_glEquiv_transvection (t : Matrix.TransvectionStruct ι F)
    (h : t.toMatrix.det ≠ 0) :
    distribHaarChar (ι → F) (glEquiv (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h)) = 1 := by
  classical
  obtain ⟨i, j, hij, c⟩ := t
  have h1 : ∀ d : F, (Matrix.transvection i j d).det ≠ 0 := fun d => by
    rw [Matrix.det_transvection_of_ne _ _ hij]
    exact one_ne_zero
  let T : F → GL ι F := fun d => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (h1 d)
  have hT : ∀ d d', T d * T d' = T (d + d') := fun d d' => by
    ext : 1
    simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.transvection_mul_transvection_same (h := hij)]
  have hT1 : distribHaarChar (ι → F) (glEquiv (T 1)) = 1 := by
    have hinv : (T 1)⁻¹ = T (-1) := by
      rw [inv_eq_iff_mul_eq_one, hT, add_neg_cancel]
      ext : 1
      simp [T, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    refine distribHaarChar_glEquiv_eq_one (fun a b => ?_) (fun a b => ?_)
    · exact transvection_mem_integer (Subring.one_mem _) a b
    · rw [hinv]
      exact transvection_mem_integer (Subring.neg_mem _ (Subring.one_mem _)) a b
  change distribHaarChar (ι → F) (glEquiv (T c)) = 1
  by_cases hc : c = 0
  · have : T c = 1 := by
      ext : 1
      simp [T, hc, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [this, map_one, map_one]
  let d : ι → F := Function.update 1 i c
  have hd : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
    by_cases hk : k = i
    · subst hk; simpa [d] using hc
    · simp [d, hk]
  let Dg : GL ι F := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
  have hM : Matrix.transvection i j c * Matrix.diagonal d =
      Matrix.diagonal d * Matrix.transvection i j 1 := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, d]
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · subst hai; simp [Ne.symm hij]
      · simp [hai, Ne.symm hai]
    · by_cases hai : a = i
      · subst hai
        by_cases hbj : b = j
        · subst hbj; simp [hab, Ne.symm hij]
        · simp [hab, Ne.symm hbj]
      · simp [hab, hai, Ne.symm hai]
  have hcomm : T c * Dg = Dg * T 1 := by
    ext : 1
    simpa [T, Dg, Matrix.GeneralLinearGroup.mkOfDetNeZero] using hM
  have key := congrArg (fun g => distribHaarChar (ι → F) (glEquiv g)) hcomm
  simp only [map_mul, hT1, mul_one] at key
  have hpos : distribHaarChar (ι → F) (glEquiv Dg) ≠ 0 := distribHaarChar_pos.ne'
  rw [mul_comm] at key
  exact (mul_eq_left₀ hpos).1 key

theorem distribHaarChar_glEquiv (g : GL ι F) :
    distribHaarChar (ι → F) (glEquiv g) = distribHaarChar F (Matrix.GeneralLinearGroup.det g) := by
  let φ : GL ι F →* ℝ≥0 := (distribHaarChar (ι → F)).comp glEquiv.toMonoidHom
  let ψ : GL ι F →* ℝ≥0 := (distribHaarChar F).comp Matrix.GeneralLinearGroup.det
  have key : ∀ (M : Matrix ι ι F) (h : M.det ≠ 0),
      φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) := by
    intro M hM
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∀ h : M.det ≠ 0, φ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h) =
        ψ (Matrix.GeneralLinearGroup.mkOfDetNeZero M h)) M hM ?_ ?_ ?_ hM
    · intro D _ h
      exact distribHaarChar_glEquiv_diagonal h
    · intro t h
      have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ h) = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]
      change distribHaarChar (ι → F) (glEquiv _) = distribHaarChar F _
      rw [distribHaarChar_glEquiv_transvection t h, hdet, map_one]
    · intro A B hA hB IHA IHB h
      have : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) h =
          Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
            Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
        ext : 1
        rfl
      rw [this, map_mul, map_mul, IHA hA, IHB hB]
  have hg : Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix ι ι F)
      (Matrix.det_ne_zero_of_left_inverse (g.inv_mul)) = g := by
    ext : 1
    rfl
  have := key _ (Matrix.det_ne_zero_of_left_inverse (g.inv_mul))
  rw [hg] at this
  exact this

theorem distribHaarChar_pi_eq (L : (ι → F) ≃ₗ[F] (ι → F)) :
    distribHaarChar (ι → F) L = distribHaarChar F (LinearEquiv.det L) := by
  obtain ⟨g, rfl⟩ := glEquiv.surjective L
  rw [distribHaarChar_glEquiv, det_glEquiv]

end Modulus

end Measures

end GroundTheory.Automorphic
