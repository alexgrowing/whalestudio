import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import GroundTheory.AutomorphicForms.ReductionCore
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.AutomorphicForms.HaarSK
import GroundTheory.HeightsAndTheta.Theta.FundDomain

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise

namespace UpperTheory.ConvolutionTheory.R2

variable {F : Type} [Field F] [NumberField F]

instance : SecondCountableTopology (G1 F) :=
  TopologicalSpace.Subtype.secondCountableTopology {M : Matrix (Fin 2) (Fin 2) (A F) | M.det = 1}

instance : LocallyCompactSpace (G1 F) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (A F)) := inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A F))
  have h : IsClosed {M : Matrix (Fin 2) (Fin 2) (A F) | M.det = 1} :=
    isClosed_eq (continuous_id.matrix_det) continuous_const
  exact h.locallyCompactSpace

namespace M

theorem ab_pos (a : (A F)ˣ) : 0 < ab a := (IdeleGroup.ideleModule F a).2
theorem ab_mul (a b : (A F)ˣ) : ab (a * b) = ab a * ab b := by simp [ab]
theorem ab_one : ab (1 : (A F)ˣ) = 1 := by simp [ab]
theorem ab_inv (a : (A F)ˣ) : ab a⁻¹ = (ab a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← ab_mul, inv_mul_cancel, ab_one])
theorem continuous_ab : Continuous (ab : (A F)ˣ → ℝ) :=
  continuous_subtype_val.comp (IdeleGroup.continuous_ideleModule (K := F))

theorem val_mul (g h : G1 F) : (g * h).1 = g.1 * h.1 := rfl
theorem val_gl (g : G1 F) : (gl g).val = g.1 := rfl
theorem val_ratS (γ : Matrix.SpecialLinearGroup (Fin 2) F) : (ratS F γ).1 = γ.1.map (algebraMap F (A F)) := rfl

theorem nU_add (a b : A F) : nU (a + b) = nU a * nU b := by
  refine Subtype.ext ?_; rw [val_mul]; ext i j; fin_cases i <;> fin_cases j <;> simp [nU, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
theorem nU_zero : nU (0 : A F) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nU]
theorem nU_neg (a : A F) : nU (-a) = (nU a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← nU_add, neg_add_cancel, nU_zero])
theorem mD_mul (a b : (A F)ˣ) : mD (a * b) = mD a * mD b := by
  refine Subtype.ext ?_; rw [val_mul]; ext i j; fin_cases i <;> fin_cases j <;> simp [mD, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
theorem mD_one : mD (1 : (A F)ˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mD]
theorem mD_inv (a : (A F)ˣ) : mD a⁻¹ = (mD a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← mD_mul, inv_mul_cancel, mD_one])
theorem mD_mul_nU (a : (A F)ˣ) (b : A F) : mD a * nU b = nU ((a : A F) ^ 2 * b) * mD a := by
  refine Subtype.ext ?_; rw [val_mul, val_mul]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [mD, nU, Matrix.mul_apply, Fin.sum_univ_two, pow_two, mul_assoc, mul_comm b]
theorem gl_cD (t : (A F)ˣ) (g : G1 F) : gl (cD t g) * dM t = dM t * gl g := by
  refine Units.ext ?_; rw [Units.val_mul, Units.val_mul, val_gl, val_gl]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [cD, dM, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, mul_comm]
theorem gl_inj : Function.Injective (gl : G1 F → GL (Fin 2) (A F)) := Matrix.SpecialLinearGroup.toGL_injective
theorem gl_cD' (t : (A F)ˣ) (g : G1 F) : gl (cD t g) = dM t * gl g * (dM t)⁻¹ := by
  rw [← gl_cD, mul_inv_cancel_right]
theorem dM_mul (s t : (A F)ˣ) : dM (s * t) = dM s * dM t := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dM, Matrix.mul_apply, Fin.sum_univ_two]
theorem dM_one : dM (1 : (A F)ˣ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dM]
theorem cD_mul (t : (A F)ˣ) (g h : G1 F) : cD t (g * h) = cD t g * cD t h :=
  gl_inj (by
    have h : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
    rw [h, gl_cD', gl_cD', gl_cD', h]; group)
theorem cD_cD (s t : (A F)ˣ) (g : G1 F) : cD s (cD t g) = cD (s * t) g :=
  gl_inj (by rw [gl_cD', gl_cD', gl_cD', dM_mul]; group)
theorem cD_one (g : G1 F) : cD 1 g = g := gl_inj (by rw [gl_cD', dM_one]; group)
theorem cD_nU (t : (A F)ˣ) (b : A F) : cD t (nU b) = nU (b * ((t⁻¹ : (A F)ˣ) : A F)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cD, nU]
theorem cD_mD (t a : (A F)ˣ) : cD t (mD a) = mD a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cD, mD]
theorem cD_sq (t : (A F)ˣ) (g : G1 F) : cD (t * t) g = (mD t)⁻¹ * g * mD t := by
  rw [← mD_inv]
  refine Subtype.ext ?_; rw [val_mul, val_mul]; ext i j; fin_cases i <;> fin_cases j <;>
    simp [cD, mD, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, mul_assoc, mul_comm, mul_left_comm]

theorem continuous_nU : Continuous (nU : A F → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by fin_cases i <;> fin_cases j <;> simp <;> fun_prop) _
theorem continuous_mD : Continuous (mD : (A F)ˣ → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      first | exact continuous_const | exact Units.continuous_val | exact Units.continuous_coe_inv) _
theorem continuous_entry (i j : Fin 2) : Continuous fun g : G1 F => g i j :=
  (continuous_subtype_val (p := fun M : Matrix (Fin 2) (Fin 2) (A F) => M.det = 1)).matrix_elem i j
theorem continuous_cD (t : (A F)ˣ) : Continuous (cD t : G1 F → G1 F) :=
  Continuous.subtype_mk (continuous_matrix fun i j => by
    fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;>
      first | exact continuous_entry _ _ | exact (continuous_entry _ _).mul continuous_const | exact continuous_const.mul (continuous_entry _ _)) _
theorem continuous_gl : Continuous (gl : G1 F → GL (Fin 2) (A F)) := Matrix.SpecialLinearGroup.continuous_toGL

theorem ratS_up (ξ : F) : ratS F ⟨!![1, ξ; 0, 1], by simp [Matrix.det_fin_two]⟩ = nU (rt ξ) := by
  refine Subtype.ext ((val_ratS _).trans ?_); ext i j; fin_cases i <;> fin_cases j <;> simp [nU]
theorem nU_rt_mem (ξ : F) : nU (rt ξ) ∈ Gam F := ⟨_, ratS_up ξ⟩
theorem mD_diag_mem (t : Fˣ) : mD (IdeleGroup.diagonal F t) ∈ Gam F := by
  refine ⟨⟨!![(t : F), 0; 0, ((t⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, ?_⟩
  refine Subtype.ext ((val_ratS _).trans ?_); ext i j; fin_cases i <;> fin_cases j <;> simp [mD, IdeleGroup.diagonal, ← map_inv]
theorem ab_diag (t : Fˣ) : ab (IdeleGroup.diagonal F t) = 1 := by
  simp [ab, IdeleGroup.ideleModule_diagonal]

instance : Countable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  exact inferInstanceAs (Countable {M : Matrix (Fin 2) (Fin 2) F // M.det = 1})
instance : Countable (Gam F) := (Set.countable_range _).to_subtype

instance : DiscreteTopology (Gam F) := by
  haveI := AdelicGLn.discreteTopology_rationalGL F 2
  have hm : ∀ g : Gam F, gl g.1 ∈ AdelicGLn.rationalGL F 2 := by
    rintro ⟨_, γ, rfl⟩
    exact ⟨Matrix.SpecialLinearGroup.toGL γ, Units.ext rfl⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun g : Gam F => (⟨gl g.1, hm g⟩ : AdelicGLn.rationalGL F 2)) ?_
    fun a b h => Subtype.ext (gl_inj (congrArg (·.1) h))
  exact (continuous_gl.comp continuous_subtype_val).subtype_mk _

variable (F) in

def Ks : Subgroup (G1 F) := (Reduction.maxCompact (K := F) (n := 2)).comap Matrix.SpecialLinearGroup.toGL
variable (F) in

def Bor : Subgroup (G1 F) := (Reduction.adelicBorel (K := F) (n := 2)).comap Matrix.SpecialLinearGroup.toGL

def wt (a : (A F)ˣ) : ℝ≥0∞ := ENNReal.ofReal ((ab a)⁻¹ ^ 2)

def J0 (M : Meas F) (u : G1 F → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ p, wt p.1 * u (mD p.1 * p.2) ∂M.ν

def NWt (β : G1 F → ℝ≥0∞) : Prop := Measurable β ∧ ∀ g, ∑' ξ : F, β (nU (rt ξ) * g) = 1

def RowSec (σ : {r : Fin 2 → F // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) F) : Prop := ∀ r, (σ r).1 1 = r.1

theorem measurable_wt : Measurable (wt : IdeleGroup F → ℝ≥0∞) :=
  ((continuous_ab.measurable.inv).pow_const 2).ennreal_ofReal

theorem transfer {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {m : Measure X} {n : Measure Y} {u : X → ℂ} {v : Y → ℂ}
    (hu : Measurable u) (hv : Measurable v)
    (h : ∀ φ : ℂ → ℝ≥0∞, Measurable φ → ∫⁻ x, φ (u x) ∂m = ∫⁻ y, φ (v y) ∂n) :
    (Integrable u m ↔ Integrable v n) ∧ ∫ x, u x ∂m = ∫ y, v y ∂n := by
  have e : m.map u = n.map v := by
    ext s hs
    rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map (measurable_one.indicator hs) hu,
      lintegral_map (measurable_one.indicator hs) hv]
    exact h _ (measurable_one.indicator hs)
  constructor
  · have h1 := integrable_map_measure (μ := m) (f := u) (g := id) aestronglyMeasurable_id hu.aemeasurable
    have h2 := integrable_map_measure (μ := n) (f := v) (g := id) aestronglyMeasurable_id hv.aemeasurable
    rw [e] at h1
    exact h1.symm.trans h2
  · have h1 := integral_map (μ := m) (φ := u) (f := id) hu.aemeasurable aestronglyMeasurable_id
    have h2 := integral_map (μ := n) (φ := v) (f := id) hv.aemeasurable aestronglyMeasurable_id
    rw [e] at h1
    exact h1.symm.trans h2

end M

end UpperTheory.ConvolutionTheory.R2

end
