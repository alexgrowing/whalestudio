import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMapContractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFrameAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReframeVerticalDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoebImaginaryPartTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnitStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff

namespace GlobalTheory.TorsionForm.Gauge.AdjConj

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem smul_decomp {V : Type} [AddCommGroup V] [Module ℂ V] (z : ℂ) (v : V) :
    z • v = z.re • v + z.im • (Complex.I • v) := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]

theorem d10_smul {m : ℕ} (f : Pt E g → Ext m) (P v : Pt E g) (z : ℂ) :
    d10 f P (z • v) = z • d10 f P v := by
  rw [smul_decomp z v, Pullback.dz_add_vector, Pullback.dz_real_smul, Pullback.dz_real_smul, Pullback.dz_smul_I,
    smul_decomp z (d10 f P v)]

theorem d10_smul' (f : Pt E g → ℂ) (P v : Pt E g) (z : ℂ) :
    d10 f P (z • v) = z • d10 f P v := by
  rw [smul_decomp z v, Pullback.dz_add_vector_scalar, Pullback.dz_real_smul_scalar, Pullback.dz_real_smul_scalar, Pullback.dz_smul_I_scalar,
    smul_decomp z (d10 f P v)]

theorem d10_finsum {m : ℕ} (f : Pt E g → Ext m) (P : Pt E g) (v : Fin g → Pt E g)
    (S : Finset (Fin g)) : d10 f P (∑ c ∈ S, v c) = ∑ c ∈ S, d10 f P (v c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [d10]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Pullback.dz_add_vector, ih]

theorem d10_finset_sum (f : Pt E g → ℂ) (P : Pt E g) (v : Fin g → Pt E g)
    (S : Finset (Fin g)) : d10 f P (∑ c ∈ S, v c) = ∑ c ∈ S, d10 f P (v c) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [d10]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Pullback.dz_add_vector_scalar, ih]

theorem d10_finset_sum' {m : ℕ} (f : Pt E g → Ext m) (P : Pt E g) (x : Fin g → ℂ) :
    d10 f P (∑ c, x c • vert E c) = ∑ c, x c • d10 f P (vert E c) := by
  rw [d10_finsum]; simp only [d10_smul]

theorem d10_sum_smul_vert (f : Pt E g → ℂ) (P : Pt E g) (x : Fin g → ℂ) :
    d10 f P (∑ c, x c • vert E c) = ∑ c, x c • d10 f P (vert E c) := by
  rw [d10_finset_sum]; simp only [d10_smul']

theorem contr_smul {m : ℕ} (i : Fin m) (c : ℂ) (w : Ext m) : contr i (c • w) = c • contr i w := by
  funext S; simp only [contr, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

def contrL {m : ℕ} (i : Fin m) : Ext m →ₗ[ℂ] Ext m where
  toFun := contr i
  map_add' := Pullback.contr_add i
  map_smul' := contr_smul i

theorem contr_sum {m : ℕ} (i : Fin m) (x : Fin g → Ext m) :
    contr i (∑ c, x c) = ∑ c, contr i (x c) :=
  map_sum (contrL i) x Finset.univ

theorem sum_sum_sum_sum_comm {X : Type} [AddCommMonoid X] (F : Fin g → Fin g → Fin g → Fin g → X) :
    ∑ a, ∑ c, ∑ e, ∑ d, F a c e d = ∑ e, ∑ d, ∑ a, ∑ c, F a c e d := by
  calc ∑ a, ∑ c, ∑ e, ∑ d, F a c e d = ∑ a, ∑ e, ∑ c, ∑ d, F a c e d := by
        congr 1; funext a; exact Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ c, ∑ d, F a c e d := Finset.sum_comm
    _ = ∑ e, ∑ a, ∑ d, ∑ c, F a c e d := by
        congr 1; funext e; congr 1; funext a; exact Finset.sum_comm
    _ = ∑ e, ∑ d, ∑ a, ∑ c, F a c e d := by
        congr 1; funext e; exact Finset.sum_comm

theorem d10_comp_continuousLinearMap {m : ℕ} (f : Pt E g → Ext m) (R : Pt E g → Pt E g) (P v : Pt E g)
    (hR : DifferentiableAt ℂ R P) (hf : DifferentiableAt ℝ f (R P)) :
    d10 (fun Q => f (R Q)) P v = d10 f (R P) (fderiv ℝ R P v) := by
  have hc : fderiv ℝ (fun Q => f (R Q)) P = (fderiv ℝ f (R P)).comp (fderiv ℝ R P) :=
    fderiv_comp P hf (hR.restrictScalars ℝ)
  have hRr : fderiv ℝ R P = (fderiv ℂ R P).restrictScalars ℝ := hR.fderiv_restrictScalars ℝ
  simp only [d10, hc, ContinuousLinearMap.comp_apply, hRr, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem d10_comp_of_differentiableAt (f : Pt E g → ℂ) (R : Pt E g → Pt E g) (P v : Pt E g)
    (hR : DifferentiableAt ℂ R P) (hf : DifferentiableAt ℝ f (R P)) :
    d10 (fun Q => f (R Q)) P v = d10 f (R P) (fderiv ℝ R P v) := by
  have hc : fderiv ℝ (fun Q => f (R Q)) P = (fderiv ℝ f (R P)).comp (fderiv ℝ R P) :=
    fderiv_comp P hf (hR.restrictScalars ℝ)
  have hRr : fderiv ℝ R P = (fderiv ℂ R P).restrictScalars ℝ := hR.fderiv_restrictScalars ℝ
  simp only [d10, hc, ContinuousLinearMap.comp_apply, hRr, ContinuousLinearMap.coe_restrictScalars',
    map_smul]

theorem fderiv_gauge_vert (n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g)
    (s : Pt E g → Ext (n + n + g)) (P : Pt E g)
    (hA : DifferentiableAt ℝ (fun b => frameAt n τ γ b) P.1)
    (hu : DifferentiableAt ℝ (fun Q => s (reframe τ γ Q)) P) (w : Fin g → ℂ) :
    fderiv ℝ (gauge n τ γ s) P ((0 : E), w) =
      frameAt n τ γ P.1 (fderiv ℝ (fun Q => s (reframe τ γ Q)) P (0, w)) := by
  let L := ContinuousLinearMap.restrictScalarsL ℂ (Ext (n + n + g)) (Ext (n + n + g)) ℝ ℝ
  have hc : HasFDerivAt (fun Q : Pt E g => L (frameAt n τ γ Q.1))
      (L.comp ((fderiv ℝ (fun b => frameAt n τ γ b) P.1).comp (ContinuousLinearMap.fst ℝ E (Fin g → ℂ)))) P :=
    L.hasFDerivAt.comp P (hA.hasFDerivAt.comp P (hasFDerivAt_fst))
  have h2 := hc.clm_apply hu.hasFDerivAt
  have e : gauge n τ γ s = fun Q => (L (frameAt n τ γ Q.1)) (s (reframe τ γ Q)) := rfl
  rw [e, h2.fderiv]
  simp [L]

end GlobalTheory.TorsionForm.Gauge.AdjConj

namespace GlobalTheory.TorsionForm.Gauge.AdjConj

theorem contr_frameMap {g : ℕ} (n : ℕ) (D : Matrix (Fin g) (Fin g) ℂ) (hD : IsUnit D) (c : Fin g)
    (w : Ext (n + n + g)) :
    contr (dzb n c) (frameMap n D w) = ∑ d, star (D⁻¹ c d) • frameMap n D (contr (dzb n d) w) := by
  have hinv : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hD)
  simp only [GlobalTheory.T.frameMap_contraction n _ hD, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have e' : ∀ a, star ((1 : Matrix (Fin g) (Fin g) ℂ) c a) = (1 : Matrix (Fin g) (Fin g) ℂ) c a :=
    fun a => by rw [Matrix.one_apply]; split_ifs <;> simp
  have e : ∀ a, ∑ d, star (D⁻¹ c d) * star (D d a) = if c = a then 1 else 0 := by
    intro a
    rw [← Matrix.one_apply, ← e', ← hinv, Matrix.mul_apply, star_sum]
    simp only [star_mul']
  simp only [e, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.TorsionForm.Gauge.AdjConj

namespace GlobalTheory.TorsionForm.Gauge.AdjConj

theorem dbarAdj_gauge {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ)
    (s : Pt E g → Ext (n + n + g)) (hτ : IsPeriodMap B τ)
    (hτ' : IsPeriodMap B (fun b => moeb γ (τ b))) (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hpos : ∀ P ∈ cov B g, 0 < h P) (hs : DifferentiableOn ℝ s (cov B g)) :
    ∀ P ∈ cov B g, dbarAdj τ (fun Q => h (reframe τ γ Q)) (gauge n τ γ s) P =
      frameAt n τ γ P.1 (dbarAdj (fun b => moeb γ (τ b)) h s (reframe τ γ P)) := by
  intro P hP
  have hb : P.1 ∈ B := hP.1
  have hcovOpen : IsOpen (cov B g) := hτ.1.prod isOpen_univ
  have hRP : reframe τ γ P ∈ cov B g := ⟨hb, trivial⟩
  have hD : IsUnit (den γ (τ P.1)) := GlobalTheory.T.period_map_moebius_denom_unit B τ γ hτ' P.1 hb
  obtain ⟨hRc, hRv⟩ := GlobalTheory.T.reframe_vertical_derivative B τ γ hτ hτ' P hP
  have hA : DifferentiableAt ℝ (fun b => frameAt n τ γ b) P.1 :=
    ((GlobalTheory.T.contDiffOn_frameAt_of_isPeriodMap n B τ γ hτ hτ').contDiffAt (hτ.1.mem_nhds hb)).differentiableAt (by simp)
  have hsR : DifferentiableAt ℝ s (reframe τ γ P) := hs.differentiableAt (hcovOpen.mem_nhds hRP)
  have hu : DifferentiableAt ℝ (fun Q => s (reframe τ γ Q)) P := hsR.comp P (hRc.restrictScalars ℝ)
  have hhR : DifferentiableAt ℝ h (reframe τ γ P) :=
    ((hh.contDiffAt (hcovOpen.mem_nhds hRP)).differentiableAt (by simp))
  have hlog : DifferentiableAt ℝ (fun Q => (Real.log (h Q) : ℂ)) (reframe τ γ P) :=
    Complex.ofRealCLM.differentiableAt.comp _ (hhR.log (hpos _ hRP).ne')

  have hd10g : ∀ a : Fin g, d10 (gauge n τ γ s) P (vert E a) =
      frameAt n τ γ P.1 (d10 (fun Q => s (reframe τ γ Q)) P (vert E a)) := by
    intro a
    have e1 : Complex.I • vert E a = ((0 : E), Complex.I • (Pi.single a 1 : Fin g → ℂ)) := by
      simp [vert]
    simp only [d10, e1]
    rw [vert, fderiv_gauge_vert n τ γ s P hA hu, fderiv_gauge_vert n τ γ s P hA hu]
    simp only [map_smul, map_sub]
  have key : ∀ a, pointDifference (fun Q => h (reframe τ γ Q)) (gauge n τ γ s) P (vert E a) =
      ∑ e, (den γ (τ P.1))⁻¹ a e • frameAt n τ γ P.1 (pointDifference h s (reframe τ γ P) (vert E e)) := by
    intro a
    simp only [pointDifference, hd10g]
    rw [d10_comp_continuousLinearMap s (reframe τ γ) P _ hRc hsR,
      d10_comp_of_differentiableAt (fun Q => (Real.log (h Q) : ℂ)) (reframe τ γ) P _ hRc hlog, hRv, d10_finset_sum', d10_sum_smul_vert]
    simp only [pointDifference, map_sum, map_add, map_smul, Finset.sum_smul, smul_add,
      Finset.sum_add_distrib, smul_smul, gauge, smul_eq_mul]
  have contrΦ : ∀ (c : Fin g) (w : Ext (n + n + g)), contr (dzb n c) (frameAt n τ γ P.1 w) =
      ∑ d, star ((den γ (τ P.1))⁻¹ c d) • frameAt n τ γ P.1 (contr (dzb n d) w) :=
    fun c w => contr_frameMap n _ hD c w
  have hr : ∀ (M : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g),
      star (M.map (fun t => (t.im : ℂ)) i j) = M.map (fun t => (t.im : ℂ)) i j := by
    intro M i j; simp [Complex.conj_ofReal]
  have hsym : (τ P.1).IsSymm := (hτ.2.2 P.1 hb).1
  have hIm := GlobalTheory.T.moeb_imaginary_part_transform γ (τ P.1) hsym hD
  have hY : ∀ e d, imPart (fun b => moeb γ (τ b)) P.1 e d = ∑ a, ∑ c,
      (den γ (τ P.1))⁻¹ a e * imPart τ P.1 a c * star ((den γ (τ P.1))⁻¹ c d) := by
    intro e d
    have e1 : imPart (fun b => moeb γ (τ b)) P.1 e d =
        star (((((den γ (τ P.1))⁻¹)ᴴ * imPart τ P.1) * (den γ (τ P.1))⁻¹) e d) := by
      simp only [imPart]; rw [← hIm, hr]
    have hr' : ∀ i j, star (imPart τ P.1 i j) = imPart τ P.1 i j := hr (τ P.1)
    rw [e1]
    simp only [Matrix.mul_apply, conjTranspose_apply, star_sum, star_mul', star_star, hr',
      Finset.sum_mul]
    rw [Finset.sum_comm]
  have hdbar : dbarAdj (fun b => moeb γ (τ b)) h s (reframe τ γ P) =
      -∑ e, ∑ d, (2 * imPart (fun b => moeb γ (τ b)) P.1 e d) •
        contr (dzb n d) (pointDifference h s (reframe τ γ P) (vert E e)) := rfl
  rw [hdbar]
  simp only [dbarAdj, key, contr_sum, contr_smul, contrΦ, hY, map_neg, map_sum, map_smul]
  congr 1
  simp only [Finset.smul_sum, smul_smul, Finset.mul_sum, Finset.sum_smul]
  rw [sum_sum_sum_sum_comm]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  ring

end GlobalTheory.TorsionForm.Gauge.AdjConj
