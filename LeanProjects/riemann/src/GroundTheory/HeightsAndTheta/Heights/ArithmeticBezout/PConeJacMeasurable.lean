import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeJacMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTangentJacCompress
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsKernelProjMeasurable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

variable {n : ℕ}

def coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : Matrix (Fin k) (Fin n) ℂ :=
  Matrix.of (fun i j => eval (h.pointOf y) (pderiv j (g i))) * h.mat.transpose

theorem continuous_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ) :
    Continuous (coneJacMat h g) := by
  unfold coneJacMat
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (MvPolynomial.continuous_eval _).comp h.continuous_pointOf

theorem mem_ker_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y v : EuclideanSpace ℂ (Fin n)) :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) ↔
      ∀ i, ∑ j, eval (h.pointOf y) (pderiv j (g i)) * h.pointOf v j = 0 := by
  rw [LinearMap.mem_ker]
  change WithLp.toLp 2 (Matrix.mulVec (coneJacMat h g y) (WithLp.ofLp v)) = 0 ↔ _
  rw [WithLp.toLp_eq_zero, coneJacMat, ← Matrix.mulVec_mulVec, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rfl

theorem coneTangent_eq_ker (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ}
    (g : Fin k → MvPolynomial (Fin n) ℂ) (hg : Submodule.span _ (Set.range g) = J)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    coneTangent h J y = LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) := by
  ext v
  rw [mem_ker_coneJacMat]
  constructor
  · intro hv i
    exact hv (g i) (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro hv q hq
    rw [← hg] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv i
    | zero => simp
    | add x z _ _ hx hz => simp [add_mul, Finset.sum_add_distrib, hx, hz]
    | smul a x hxmem hx =>
      have hx0 : eval (h.pointOf y) x = 0 := hy x (hg ▸ hxmem)
      calc ∑ j, eval (h.pointOf y) (pderiv j (a • x)) * h.pointOf v j
          = eval (h.pointOf y) a * ∑ j, eval (h.pointOf y) (pderiv j x) * h.pointOf v j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_eq_mul, pderiv_mul, map_add, map_mul, map_mul, hx0]
            ring
        _ = 0 := by rw [hx, mul_zero]

theorem coneTangent_eq_bot (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∉ coneSet h J) : coneTangent h J y = ⊥ := by
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ J, eval (h.pointOf y) q ≠ 0 := by
    simpa [coneSet] using hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  apply h.pointOf_eq_zero
  funext l
  have h1 : ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0 := hv q hq
  have h2 : ∑ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j = 0 :=
    hv _ (J.mul_mem_left _ hq)
  have h3 : ∀ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j =
      h.pointOf y l * (eval (h.pointOf y) (pderiv j q) * h.pointOf v j) +
        if l = j then eval (h.pointOf y) q * h.pointOf v l else 0 := by
    intro j
    by_cases hj : l = j
    · subst hj
      simp
      ring
    · simp [pderiv_X_of_ne hj, hj]
      ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  exact (mul_eq_zero.1 h2).resolve_left hq0

theorem starProjection_congr {U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (e : U = V) :
    U.starProjection = V.starProjection := by
  subst e
  rfl

def gramOp {m : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L LinearMap.toContinuousLinearMap (linProjₗ π)

theorem continuous_gramOp (m : ℕ) : Continuous (gramOp (n := n) (m := m)) := by
  have hL : Continuous fun π : Fin m → Fin n → ℂ =>
      LinearMap.toContinuousLinearMap (linProjₗ π) := by
    refine continuous_clm_apply.2 fun v => ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    change Continuous fun π : Fin m → Fin n → ℂ => linProj π v
    unfold linProj
    fun_prop
  exact (ContinuousLinearMap.adjoint.continuous.comp hL).clm_comp hL

def compressDet {m : ℕ} (π : Fin m → Fin n → ℂ)
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Complex.re (Q ∘L gramOp π ∘L Q + (1 - Q)).det

theorem continuous_compressDet (m : ℕ) :
    Continuous fun p : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet p.1 p.2 :=
  Complex.continuous_re.comp (ContinuousLinearMap.continuous_det.comp
    ((continuous_snd.clm_comp (((continuous_gramOp m).comp continuous_fst).clm_comp
      continuous_snd)).add (continuous_const.sub continuous_snd)))

theorem coneJac_eq_compressDet (hComp : TangentJacCompress.Statement) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) {m : ℕ} (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    coneJac h J π y = compressDet π (coneTangent h J y).starProjection := by
  rw [coneJac, compressDet, gramOp, ContinuousLinearMap.comp_assoc, ← hComp n m π (coneTangent h J y), Complex.ofReal_re]

theorem ConeJacMeasurable.proof (hComp : TangentJacCompress.Statement)
    (hKer : KernelProjMeasurable.Statement) : ConeJacMeasurable.Statement := by
  classical
  intro n m h J _ _ _ _
  refine Measurable.aemeasurable ?_
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)
  let P : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    (coneSet h J).piecewise
      (fun y => (LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y))).starProjection) 0
  have hP : Measurable P :=
    Measurable.piecewise (isClosed_coneSet h J).measurableSet
      (hKer (EuclideanSpace ℂ (Fin n)) n k _ (continuous_coneJacMat h g)) measurable_const
  have hTP : ∀ y, (coneTangent h J y).starProjection = P y := by
    intro y
    by_cases hy : y ∈ coneSet h J
    · simp only [P, Set.piecewise_eq_of_mem _ _ _ hy]
      exact starProjection_congr (coneTangent_eq_ker h g hg hy)
    · simp only [P, Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [starProjection_congr (coneTangent_eq_bot h hy), Submodule.starProjection_bot]
      rfl
  have hJac : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => coneJac h J p.1 p.2) =
      fun p => compressDet p.1 (P p.2) := by
    funext p
    rw [coneJac_eq_compressDet hComp, hTP]
  have hM : Measurable fun q : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet q.1 q.2 :=
    (continuous_compressDet m).measurable
  have hM2 : Measurable fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => (p.1, P p.2) :=
    measurable_fst.prodMk (hP.comp measurable_snd)
  have hM3 := hM.comp hM2
  rw [hJac]
  exact hM3

end

end GroundTheory.Heights₂.Heights
