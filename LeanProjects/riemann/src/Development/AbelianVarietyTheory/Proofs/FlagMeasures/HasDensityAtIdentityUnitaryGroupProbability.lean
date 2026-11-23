import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueHaarDensityAtIdentityStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarVolumeThinTubeUnitaryProductAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarUnitaryLastDiagonalEntryLawStatement

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.UnitaryVolume

theorem mem_UH_one {m : ℕ} {g : Matrix (Fin m) (Fin m) ℂ} :
    g ∈ UH (1 : Matrix (Fin m) (Fin m) ℂ) ↔ gᴴ * g = 1 := by
  show gᴴ * 1 * g = 1 ↔ _
  rw [Matrix.mul_one]

theorem UH_one_eq (m : ℕ) : UH (1 : Matrix (Fin m) (Fin m) ℂ) =
    (Matrix.unitaryGroup (Fin m) ℂ : Set (Matrix (Fin m) (Fin m) ℂ)) := by
  ext g
  rw [mem_UH_one, SetLike.mem_coe, Matrix.mem_unitaryGroup_iff']
  rfl

theorem isCompact_UH_one (m : ℕ) : IsCompact (UH (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  rw [UH_one_eq]; exact GlobalTheory.isCompact_unitaryGroup _ _

theorem isMatGroup_UH_one (m : ℕ) : PI.IsMatGroup (UH (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  refine ⟨(isCompact_UH_one m).isClosed, mem_UH_one.2 (by simp), fun a ha b hb => ?_, fun g hg => ?_⟩
  · rw [mem_UH_one] at *
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc aᴴ, ha, Matrix.one_mul, hb]
  · rw [mem_UH_one] at *
    have h1 : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv hg
    have h2 : g * gᴴ = 1 := mul_eq_one_comm.1 hg
    rw [h1, Matrix.conjTranspose_conjTranspose]
    exact ⟨h2, h2⟩

theorem exists_prob_haar {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : PI.IsMatGroup G) (hc : IsCompact G) :
    ∃ μ : Measure (PI.MtM m), PI.IsHaarOnM G μ ∧ μ Set.univ = 1 := by
  have hc' : IsCompact (Set.range (MatHaar.inc : MatHaar.Grp G hG → PI.MtM m)) := by
    rw [MatHaar.range_inc]; exact hc
  haveI : CompactSpace (MatHaar.Grp G hG) := ⟨by
    rw [MatHaar.inc_closedEmb.isInducing.isCompact_iff, Set.image_univ]; exact hc'⟩
  let ν : Measure (MatHaar.Grp G hG) := Measure.haarMeasure ⊤
  have hν : ν Set.univ = 1 := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (MatHaar.Grp G hG)))
  have h1 : (ν.map MatHaar.inc) Set.univ = 1 := by
    rw [MatHaar.inc_memb.map_apply, Set.preimage_univ, hν]
  haveI : IsProbabilityMeasure (ν.map MatHaar.inc) := ⟨h1⟩
  refine ⟨ν.map MatHaar.inc, ⟨inferInstance, IsProbabilityMeasure.ne_zero _, ?_, fun s hs => ?_⟩, h1⟩
  · rw [MatHaar.inc_memb.map_apply]
    have : (MatHaar.inc : MatHaar.Grp G hG → PI.MtM m) ⁻¹' {x | Matrix.of x ∉ G} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact MatHaar.inc_mem x
    rw [this, measure_empty]
  · let a : MatHaar.Grp G hG := ⟨s, hs⟩
    rw [Measure.map_map (MatHaar.lmulQ_cont s).measurable MatHaar.inc_memb.measurable]
    have : PI.lmulQ s ∘ (MatHaar.inc : MatHaar.Grp G hG → PI.MtM m) = MatHaar.inc ∘ fun x => a * x := by
      funext x; rfl
    rw [this, ← Measure.map_map MatHaar.inc_memb.measurable (measurable_const_mul a), map_mul_left_eq_self]

theorem hasDens_zero (S : Set (Matrix (Fin 0) (Fin 0) ℂ)) (μ : Measure (PI.MtM 0)) (h : μ Set.univ = 1) :
    HasDens S μ 1 := by
  haveI : Subsingleton (EuclideanSpace ℝ (Fin 0 × Fin 0 × Bool)) :=
    ⟨fun a b => by ext p; exact p.1.elim0⟩
  haveI : Subsingleton (lieE S) := inferInstance
  have hu : (volume : Measure (lieE S)) Set.univ = 1 := by
    have hp := (stdOrthonormalBasis ℝ (lieE S)).volume_parallelepiped
    have he : parallelepiped (stdOrthonormalBasis ℝ (lieE S)) = Set.univ :=
      Set.eq_univ_of_forall fun x => by
        rw [Subsingleton.elim x 0]
        exact mem_parallelepiped_iff _ _ |>.2 ⟨0, by simp, Subsingleton.elim _ _⟩
    rwa [he] at hp
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  have hb : Metric.ball (0 : lieE S) ρ = Set.univ :=
    Set.eq_univ_of_forall fun x => by
      rw [Subsingleton.elim x 0]; exact Metric.mem_ball_self hρ
  have he : expSet S Set.univ = Set.univ :=
    Set.eq_univ_of_forall fun x => ⟨0, trivial, Subsingleton.elim _ _⟩
  rw [hb, he, h, hu]; simp

local instance factTwoPi : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem mat_ext {A B : Matrix (Fin 1) (Fin 1) ℂ} (h : A 0 0 = B 0 0) : A = B := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, h]

theorem exp_one (X : Matrix (Fin 1) (Fin 1) ℂ) : NormedSpace.exp X 0 0 = Complex.exp (X 0 0) := by
  have : X = Matrix.diagonal fun _ => X 0 0 := mat_ext (by simp)
  rw [this, Matrix.exp_diagonal, Complex.exp_eq_exp_ℂ, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
    Pi.coe_exp]

theorem mem_UH_rank_one {g : Matrix (Fin 1) (Fin 1) ℂ} :
    g ∈ UH (1 : Matrix (Fin 1) (Fin 1) ℂ) ↔ ‖g 0 0‖ = 1 := by
  rw [mem_UH_one]
  have e : (gᴴ * g) 0 0 = ((‖g 0 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.conj_mul']
    push_cast; rfl
  constructor
  · intro h
    rw [h, Matrix.one_apply_eq] at e
    have : ‖g 0 0‖ ^ 2 = 1 := by exact_mod_cast e.symm
    nlinarith [norm_nonneg (g 0 0)]
  · intro h
    apply mat_ext
    rw [e, h]; simp

theorem mem_lieE_one {x : EuclideanSpace ℝ (Fin 1 × Fin 1 × Bool)} :
    x ∈ lieE (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) ↔ x (0, 0, false) = 0 := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have h1 := mem_UH_rank_one.1 (hX 1)
      rw [exp_one, Complex.norm_exp, Real.exp_eq_one_iff] at h1
      simpa [realifyFun] using h1
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  · intro h
    refine Submodule.subset_span ⟨unrealify x, fun t => ?_, ?_⟩
    · rw [mem_UH_rank_one, exp_one, Complex.norm_exp, Real.exp_eq_one_iff]
      simp [unrealify, h]
    · ext ⟨i, j, b⟩
      cases b <;> simp [realifyFun, unrealify]

def lieLine : ℝ →ₗᵢ[ℝ] lieE (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) where
  toFun s := ⟨EuclideanSpace.single (0, 0, true) s, mem_lieE_one.2 (by simp)⟩
  map_add' s t := by
    apply Subtype.ext; ext p; by_cases h : p = (0, 0, true) <;> simp [h]
  map_smul' s t := by
    apply Subtype.ext; ext p; by_cases h : p = (0, 0, true) <;> simp [h]
  norm_map' s := by
    show ‖EuclideanSpace.single (𝕜 := ℝ) ((0, 0, true) : Fin 1 × Fin 1 × Bool) s‖ = _
    simp

theorem coe_lieLine (s : ℝ) : (lieLine s : EuclideanSpace ℝ (Fin 1 × Fin 1 × Bool)) =
    EuclideanSpace.single (0, 0, true) s := rfl

theorem lieLine_surjective : Function.Surjective lieLine := by
  rintro ⟨x, hx⟩
  refine ⟨x (0, 0, true), Subtype.ext ?_⟩
  have h := mem_lieE_one.1 hx
  rw [coe_lieLine]
  ext ⟨i, j, b⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  cases b <;> simp [h]

def par (x : AddCircle (2 * Real.pi)) : PI.MtM 1 := fun _ _ => (AddCircle.toCircle x : ℂ)

theorem continuous_par : Continuous par :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_subtype_val.comp AddCircle.continuous_toCircle

theorem par_injective : Function.Injective par := fun _ _ h =>
  AddCircle.injective_toCircle Real.two_pi_pos.ne' (Circle.ext (congrFun (congrFun h 0) 0))

theorem toCircle_coe (s : ℝ) :
    AddCircle.toCircle (s : AddCircle (2 * Real.pi)) = Circle.exp s := by
  rw [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul]

theorem par_coe (s : ℝ) : par s = Matrix.of.symm (NormedSpace.exp (unrealify (lieLine s).1)) := by
  apply mat_ext
  show _ = NormedSpace.exp (unrealify (lieLine s).1) 0 0
  rw [exp_one]
  show ((AddCircle.toCircle (s : AddCircle (2 * Real.pi)) : Circle) : ℂ) = _
  rw [toCircle_coe, Circle.coe_exp]
  congr 1
  apply Complex.ext <;> simp [unrealify, coe_lieLine]

theorem par_memb : MeasurableEmbedding par :=
  (continuous_par.isClosedEmbedding par_injective).measurableEmbedding

theorem isHaar_par : PI.IsHaarOnM (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) (Measure.map par volume) := by
  refine ⟨inferInstance, fun h => ?_, ?_, fun s hs => ?_⟩
  · have := congrArg (fun ν : Measure (PI.MtM 1) => ν Set.univ) h
    simp only [par_memb.map_apply, Set.preimage_univ, AddCircle.measure_univ] at this
    simp [Real.pi_pos.not_ge] at this
  · rw [par_memb.map_apply]
    have : par ⁻¹' {x | Matrix.of x ∉ UH (1 : Matrix (Fin 1) (Fin 1) ℂ)} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [mem_UH_rank_one]
      exact Circle.norm_coe _
    rw [this, measure_empty]
  · have h1 := mem_UH_rank_one.1 hs
    obtain ⟨t, ht⟩ := Circle.exp_surjective ⟨s 0 0, by simpa [Submonoid.unitSphere] using h1⟩
    rw [Measure.map_map (MatHaar.lmulQ_cont s).measurable par_memb.measurable]
    have : PI.lmulQ s ∘ par = par ∘ fun x => (t : AddCircle (2 * Real.pi)) + x := by
      funext x
      apply mat_ext
      show (s * Matrix.of (par x)) 0 0 = ((AddCircle.toCircle ((t : AddCircle (2 * Real.pi)) + x) : Circle) : ℂ)
      rw [AddCircle.toCircle_add, toCircle_coe, Circle.coe_mul, ht]
      exact (Matrix.mul_apply ..).trans (Fin.sum_univ_one _)
    rw [this, ← Measure.map_map par_memb.measurable (measurable_const_add _), map_add_left_eq_self]

theorem preimage_arc (r : ℝ) :
    par ⁻¹' expSet (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) (Metric.ball 0 r) = Metric.ball 0 r := by
  ext x
  rw [mem_ball_zero_iff, QuotientAddGroup.norm_lt_iff]
  constructor
  · rintro ⟨X, hX, h⟩
    obtain ⟨s, rfl⟩ := lieLine_surjective X
    rw [mem_ball_zero_iff, lieLine.norm_map] at hX
    exact ⟨s, par_injective ((par_coe s).trans h), hX⟩
  · rintro ⟨s, rfl, hs⟩
    exact ⟨lieLine s, by rwa [mem_ball_zero_iff, lieLine.norm_map], (par_coe s).symm⟩

theorem volume_ball_one (r : ℝ) :
    volume (Metric.ball (0 : lieE (UH (1 : Matrix (Fin 1) (Fin 1) ℂ))) r) = ENNReal.ofReal (2 * r) := by
  let L := LinearIsometryEquiv.ofSurjective lieLine lieLine_surjective
  rw [← L.measurePreserving.measure_preimage measurableSet_ball.nullMeasurableSet, L.preimage_ball, map_zero,
    Real.volume_ball]

theorem hasDens_one (μ : Measure (PI.MtM 1)) (hμ : PI.IsHaarOnM (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) μ)
    (h : μ Set.univ = 1) :
    HasDens (UH (1 : Matrix (Fin 1) (Fin 1) ℂ)) μ (ENNReal.ofReal (2 * Real.pi)⁻¹) := by
  obtain ⟨c, -, -, hc⟩ := (MatHaar.haar_unique_locFinite_openPos 1 _ _ (isMatGroup_UH_one 1) isHaar_par).1 μ hμ
  have h1 : ∀ S, μ S = c * volume (par ⁻¹' S) := fun S => by
    rw [hc, Measure.smul_apply, smul_eq_mul, par_memb.map_apply]
  have h2 := h1 Set.univ
  rw [h, Set.preimage_univ, AddCircle.measure_univ] at h2
  have h3 : c = ENNReal.ofReal (2 * Real.pi)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos Real.two_pi_pos]
    exact ENNReal.eq_inv_of_mul_eq_one_left h2.symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with r hr
  rw [h1, preimage_arc, ← measure_congr AddCircle.closedBall_ae_eq_ball,
    AddCircle.volume_closedBall, volume_ball_one, min_eq_right (by linarith [hr.2]), ← h3,
    ENNReal.mul_div_cancel_right (by simpa using hr.1) ENNReal.ofReal_ne_top]

theorem volUn_pos (j : ℕ) : 0 < volUn j :=
  Finset.prod_pos fun i _ => by have := Real.pi_pos; positivity

theorem hasDens_unitary : ∀ (j : ℕ) (μ : Measure (PI.MtM j)), PI.IsHaarOnM (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ →
    μ Set.univ = 1 → HasDens (UH (1 : Matrix (Fin j) (Fin j) ℂ)) μ (ENNReal.ofReal (volUn j)⁻¹) := by
  intro j
  induction j with
  | zero => intro μ _ h; simpa [volUn] using hasDens_zero _ μ h
  | succ k ih =>
    intro μ hμ h
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : volUn (0 + 1) = 2 * Real.pi := by simp [volUn]
      rw [this]; exact hasDens_one μ hμ h
    obtain ⟨μ₀, hμ₀, h₀⟩ := exists_prob_haar (isMatGroup_UH_one k) (isCompact_UH_one k)
    obtain ⟨c, hc, hd, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity _ _ μ (isMatGroup_UH_one (k + 1)) hμ
    have hD : (Matrix.diagonal fun j : Fin (k + 1) => if j = Fin.last k then ((1 : ℝ) : ℂ) else 1) = 1 := by
      simp
    have hv := volUn_pos k
    have ht := GlobalTheory.T.haar_volume_thin_tube_unitary_product_asymptotic k 1 hk (Or.inl rfl) μ μ₀ c (volUn k)⁻¹ hc (inv_pos.2 hv) (by rwa [hD]) (by rwa [hD])
      hμ₀ h₀ (ih μ₀ hμ₀ h₀)
    have h1 : Tendsto (fun t : ℝ => μ {g | |‖g (Fin.last k) (Fin.last k)‖ ^ 2 - 1| ≤ t} / ENNReal.ofReal (t ^ k))
        (𝓝[>] 0) (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [GlobalTheory.T.haarUnitary_lastDiagonalEntry_law k μ hk hμ h t ht.1.le ht.2.le,
        ENNReal.div_self (by simpa using pow_pos ht.1 k) ENNReal.ofReal_ne_top]
    have h2 := ENNReal.ofReal_eq_one.1 (tendsto_nhds_unique ht h1)
    have h3 : c = (volUn (k + 1))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← h2, volUn, Finset.prod_range_succ, ← volUn]
      field_simp
    rwa [← h3]

end GlobalTheory.UnitaryVolume

end
