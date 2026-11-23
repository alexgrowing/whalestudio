import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeOneOfSumSqLtOne
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def conjKinf (k : Kinf E a) : Lie E a ≃L[ℝ] Lie E a :=
  ContinuousLinearEquiv.equivOfInverse
    ((lmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))).comp (rmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))))
    ((lmul (toL (star (k : Matrix (Fin a) (Fin a) (Cinf E))))).comp (rmul (toL (k : Matrix (Fin a) (Fin a) (Cinf E)))))
    (fun x => by
      change toL (star (k : Matrix (Fin a) (Fin a) (Cinf E)) * ((k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) * (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]; rfl)
    (fun x => by
      change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
        (Matrix.of x * (k : Matrix (Fin a) (Fin a) (Cinf E))) * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = x
      simp only [Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Unitary.mul_star_self_of_mem k.2, Matrix.one_mul]; rfl)

theorem conjKinf_apply (k : Kinf E a) (x : Lie E a) :
    conjKinf k x = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E))) := by
  change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * (Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) = _
  rw [Matrix.mul_assoc]

def frobSq (x : Lie E a) : ℝ := ∑ w, ∑ i, ∑ j, ‖x i j w‖ ^ 2

omit [NumberField E] [IsTotallyComplex E] in
theorem trace_mul_conjTranspose_cinf (M : Matrix (Fin a) (Fin a) (Cinf E)) (w : InfinitePlace E) :
    (M * M.conjTranspose).trace w = ((∑ i, ∑ j, ‖M i j w‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_apply,
    Pi.mul_apply, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem frobSq_eq (x : Lie E a) :
    frobSq x = ∑ w, ((Matrix.of x * (Matrix.of x).conjTranspose).trace w).re := by
  simp only [frobSq, trace_mul_conjTranspose_cinf, Complex.ofReal_re]; rfl

theorem frobSq_conjKinf (k : Kinf E a) (x : Lie E a) : frobSq (conjKinf k x) = frobSq x := by
  rw [frobSq_eq, frobSq_eq, conjKinf_apply]
  have h : ∀ M : Matrix (Fin a) (Fin a) (Cinf E),
      ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))) *
        ((k : Matrix (Fin a) (Fin a) (Cinf E)) * M * star (k : Matrix (Fin a) (Fin a) (Cinf E))).conjTranspose =
      (k : Matrix (Fin a) (Fin a) (Cinf E)) * (M * M.conjTranspose) * star (k : Matrix (Fin a) (Fin a) (Cinf E)) := by
    intro M
    rw [← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (k : Matrix (Fin a) (Fin a) (Cinf E))) (k : Matrix (Fin a) (Fin a) (Cinf E)),
      Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]
  rw [show Matrix.of (toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)))) =
    (k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) from rfl, h,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

theorem norm_le_one_of_frobSq (x : Lie E a) (h : frobSq x < 1) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one
  | (apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormBoundSumSquares.norm_le_one_of_sum_sq_lt_one ..)

theorem continuous_frobSq : Continuous (frobSq : Lie E a → ℝ) := by
  unfold frobSq
  fun_prop

theorem measurePreserving_conjKinf (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (k : Kinf E a) :
    MeasurePreserving (conjKinf k) ν ν := by
  refine ⟨(conjKinf k).continuous.measurable, ?_⟩
  have : ProperSpace (Lie E a) := FiniteDimensional.proper ℝ _
  have hdet : LinearMap.det ((conjKinf k : Lie E a ≃L[ℝ] Lie E a).toLinearEquiv.toLinearMap) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have e := Measure.map_linearMap_addHaar_eq_smul_addHaar ν hdet
  change Measure.map (conjKinf k) ν = _ at e
  set B : Set (Lie E a) := frobSq ⁻¹' Set.Iio 1
  have hBo : IsOpen B := isOpen_Iio.preimage continuous_frobSq
  have hB0 : (0 : Lie E a) ∈ B := by simp [B, frobSq]
  have hpos : ν B ≠ 0 := (hBo.measure_pos ν ⟨0, hB0⟩).ne'
  have hfin : ν B ≠ ⊤ := (measure_mono fun x hx => (mem_closedBall_zero_iff.2 (norm_le_one_of_frobSq x hx))).trans_lt
    (measure_closedBall_lt_top (μ := ν) (x := (0 : Lie E a)) (r := 1)) |>.ne
  have hpre : conjKinf k ⁻¹' B = B := by
    ext x; simp [B, frobSq_conjKinf]
  have h1 := congrArg (fun m : Measure (Lie E a) => m B) e
  simp only [Measure.map_apply (conjKinf k).continuous.measurable hBo.measurableSet, hpre, Measure.smul_apply,
    smul_eq_mul] at h1
  have hc := (ENNReal.mul_eq_right hpos hfin).1 h1.symm
  rw [e, hc, one_smul]

theorem smoothing_rt_Kinf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a))
    [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : KInv α) (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a) :
    smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  unfold smoothing
  rw [chart_rt_inf, chart_mul, ← (measurePreserving_conjKinf ν k).integral_comp (conjKinf k).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [Function.comp_apply]
  congr 1
  · rw [conjKinf_apply]; exact hα k x
  · congr 1
    rw [conjKinf_apply]
    change toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x * star (k : Matrix (Fin a) (Fin a) (Cinf E)) *
      (k : Matrix (Fin a) (Fin a) (Cinf E))) = toL ((k : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of x)
    rw [Matrix.mul_assoc _ (star _), Matrix.UnitaryGroup.star_mul_self, Matrix.mul_one]

end GlobalTheory.AutGrowth
