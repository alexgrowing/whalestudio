import Formalism.HermitianCurvature.StatementB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralZeroFrequencyInvariant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointnessPolynomiallyBounded
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FormalDegreeBessel.FinalBF

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B7

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section common

variable {k r : ℕ}

theorem sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, Matrix.of x ∈ U := by
  exact ae_iff.2 h.conc

def invM (x : Mt k r) : Mt k r := ((Matrix.of x : Mat k r)⁻¹ : Mat k r)

theorem measurable_invM : Measurable (invM (k := k) (r := r)) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id
  have hdet : Measurable fun x : Mt k r => (Matrix.of x : Mat k r).det := hc.matrix_det.measurable
  have hadj : ∀ i j, Measurable fun x : Mt k r => (Matrix.of x : Mat k r).adjugate i j := fun i j =>
    ((continuous_apply j).comp ((continuous_apply i).comp hc.matrix_adjugate)).measurable
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [invM, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact (measurable_inv.comp hdet).mul (hadj i j)

def mulM (x y : Mt k r) : Mt k r := Matrix.of x * Matrix.of y

theorem continuous_mulM : Continuous fun p : Mt k r × Mt k r => mulM p.1 p.2 := by
  first
    | exact Continuous.matrix_mul continuous_fst continuous_snd
    | fun_prop

theorem isClosed_GV : IsClosed {x : Mt k r | Matrix.of x ∈ GV k r} := by
  show IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r}
  refine isClosed_eq ?_ continuous_const
  first
    | fun_prop
    | exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id

theorem isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
  have hmv : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {x : Mt k r | Matrix.of x *ᵥ v = v} := fun v =>
    isClosed_eq (by first | fun_prop | exact continuous_id.matrix_mulVec continuous_const) continuous_const
  have e : {x : Mt k r | Matrix.of x ∈ UWset k r z} = {x : Mt k r | Matrix.of x ∈ GV k r} ∩
      ((⋂ a : Fin r, ({x : Mt k r | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
        {x : Mt k r | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {x : Mt k r | Matrix.of x *ᵥ z = z}) := by
    ext x
    simp only [UWset, GV, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    try tauto
  rw [e]
  exact isClosed_GV.inter ((isClosed_iInter fun a => (hmv _).inter (hmv _)).inter (hmv z))

theorem contOn_of_CkOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {F : Mat k r → E}
    (h : CkOn m (GV k r) F) : ContinuousOn F (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hfe⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfe g₀ hg₀U hg₀)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hg₀U)] with g hg hgU
  exact hfe g hgU hg

theorem meas_ind {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Zero Y] {s : Set X} (hs : MeasurableSet s)
    {f : X → Y} (hf : ContinuousOn f s) : Measurable (s.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.measurable_piecewise continuousOn_const hs

theorem sm_ind {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [SecondCountableTopology Y] {s : Set X} (hs : MeasurableSet s)
    {f : X → Y} (hf : ContinuousOn f s) : StronglyMeasurable (s.indicator f) := by
  borelize Y
  exact (meas_ind hs hf).stronglyMeasurable

theorem continuous_ell (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun x : Mt k r => ell k r z (Matrix.of x) := by
  unfold ell
  refine continuous_finset_sum _ fun a _ => ?_
  first
    | (split_ifs <;> fun_prop)
    | (by_cases h : a.val + 1 < r <;> simp [h] <;> fun_prop)
    | (split_ifs
       · exact (continuous_apply _).comp (continuous_apply _)
       · exact (continuous_apply _).comp (Continuous.matrix_mulVec continuous_id continuous_const))

theorem continuous_lam (z : Fin (2 * r + k + 1) → ℂ) : Continuous fun x : Mt k r => lam k r z (Matrix.of x) := by
  exact Complex.continuous_re.comp (continuous_const.mul (continuous_ell z))

end common

section setting

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem sfG (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μG := by
  exact sf D.haarG
theorem sfW (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μW := by
  first | exact sf D.haarW | exact sf D.haarU | exact sf D.haarUW
theorem sfN (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μN := by
  first | exact sf D.haarN | exact sf D.haarNN
theorem sfW' (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μW' := by
  first | exact sf D.haarW' | exact sf D.haarU' | exact sf D.haarUW'

attribute [local instance] sfG sfW sfN sfW'

theorem sfSS (D : RealPlaceData k r Wp Wq) : SigmaFinite D.μSS := by
  show SigmaFinite ((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
  infer_instance

attribute [local instance] sfSS

theorem ae_inSS (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  show ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p
  have q1 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.1 ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae
      (ae_mem (by first | exact D.haarW | exact D.haarU | exact D.haarUW))
  have q2 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae
      (ae_mem (by first | exact D.haarN | exact D.haarNN))
  have q3 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.1 ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae
      (ae_mem (by first | exact D.haarW' | exact D.haarU' | exact D.haarUW'))
  have q4 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae
      (ae_mem (by first | exact D.haarN | exact D.haarNN))
  filter_upwards [q1, q2, q3, q4] with p a b c d using ⟨a, b, c, d⟩

theorem continuous_xi (D : RealPlaceData k r Wp Wq) :
    Continuous fun a : (ℝ × ℝ) × SS k r => xiTau D a.1 a.2 := by
  have h : Continuous fun a : (ℝ × ℝ) × SS k r =>
      (a.1.1 * lam k r D.z (Matrix.of a.2.1.2) - a.1.2 * lam k r D.z' (Matrix.of a.2.2.2)) :=
    (continuous_fst.fst.mul ((continuous_lam D.z).comp continuous_snd.fst.snd)).sub
      (continuous_fst.snd.mul ((continuous_lam D.z').comp continuous_snd.snd.snd))
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h))

theorem norm_xi (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (p : SS k r) : ‖xiTau D τ p‖ = 1 := by
  unfold xiTau
  rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]

theorem norm_pi_le (D : RealPlaceData k r Wp Wq) {h : Mat k r} (hh : h ∈ UWset k r D.z) : ‖D.π h‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [D.π_unitary h hh v]

theorem norm_pi'_le (D : RealPlaceData k r Wp Wq) {h : Mat k r} (hh : h ∈ UWset k r D.z') : ‖D.π' h‖ ≤ 1 := by
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [D.π'_unitary h hh v]

theorem sgs_mem (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {g : Mat k r} (hg : g ∈ GV k r) :
    sgs p g ∈ GV k r := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  unfold sgs
  exact WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv h1.1) (WeylGroupFacts.uh_inv h2.1)) hg) h4.1) h3.1

theorem norm_rho_le (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (F : Mat k r → (Wq →L[ℂ] Wp))
    (g : Mat k r) : ‖rho D p F g‖ ≤ ‖F (sgs p g)‖ := by
  obtain ⟨h1, -, h3, -⟩ := hp
  unfold rho
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans ?_
  calc ‖D.π (Matrix.of p.1.1)‖ * (‖F (sgs p g)‖ * ‖D.π' (Matrix.of p.2.1)⁻¹‖)
      ≤ 1 * (‖F (sgs p g)‖ * 1) :=
        mul_le_mul (norm_pi_le D h1) (mul_le_mul_of_nonneg_left (norm_pi'_le D (WeylGroupFacts.uw_inv h3)) (norm_nonneg _))
          (by positivity) zero_le_one
    _ = ‖F (sgs p g)‖ := by ring

def Q0 (D : RealPlaceData k r Wp Wq) : Set ((Fin r → ℂ) × ℂ) :=
  {q | (∀ a, q.1 a ≠ 0) ∧ Tz k r D.z * Tz k r D.z' < Complex.normSq q.2}

theorem isOpen_good_set (D : RealPlaceData k r Wp Wq) : IsOpen (Q0 D) := by
  rw [Q0, Set.setOf_and, Set.setOf_forall]
  refine IsOpen.inter ?_ ?_
  · exact isOpen_iInter_of_finite fun a => isOpen_ne_fun ((continuous_apply a).comp continuous_fst) continuous_const
  · exact isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd)

theorem gq_mem (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) : gq D q ∈ GV k r :=
  big_cell_mem_holds k r q.1 _ hq.1 (D.sec.2 q.2 hq.2).1

def gqF (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : Mt k r := gq D q

theorem contOn_gq (D : RealPlaceData k r Wp Wq) : ContinuousOn (gqF D) (Q0 D) := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  simp only [gqF, gq, bigCell]
  split_ifs with h1 h2 h3 h4 h5
  · exact ((continuous_apply _).comp continuous_fst).continuousOn
  · exact continuousOn_const
  · exact ((D.sec.1 _ _).continuousOn).comp continuous_snd.continuousOn fun q hq => hq.2
  · exact continuousOn_const
  · refine ContinuousOn.inv₀ (continuous_star.comp ((continuous_apply _).comp continuous_fst)).continuousOn ?_
    intro q hq
    simpa using hq.1 _
  · exact continuousOn_const

def gqM (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : Mt k r :=
  (Q0 D).indicator (gqF D) q

theorem measurable_gqM (D : RealPlaceData k r Wp Wq) : Measurable (gqM D) := by
  exact meas_ind (isOpen_good_set D).measurableSet (contOn_gq D)

theorem gqM_eq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) : gqM D q = gq D q := by
  exact Set.indicator_of_mem hq _

theorem ae_mem_good_set_or_weight_zero (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, q ∈ Q0 D ∨ bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 := by
  have hc : 0 < Tz k r D.z * Tz k r D.z' := mul_pos D.T_pos D.T'_pos
  have h0 : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ Tz k r D.z * Tz k r D.z' := by
    have hs : (volume : Measure ℂ) (Metric.sphere 0 (Real.sqrt (Tz k r D.z * Tz k r D.z'))) = 0 :=
      Measure.addHaar_sphere_of_ne_zero _ _ (Real.sqrt_pos.2 hc).ne'
    refine ae_iff.2 (measure_mono_null ?_ hs)
    intro ζ hζ
    simp only [ne_eq, not_not, Set.mem_ofPred_eq] at hζ
    rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h1 : ∀ᵐ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ Tz k r D.z * Tz k r D.z' :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))).ae h0
  filter_upwards [h1] with q hq
  by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
  · exact Or.inr hw
  · left
    unfold bcWeight at hw
    split_ifs at hw with hle
    · refine ⟨fun a ha => hw ?_, lt_of_le_of_ne hle (Ne.symm hq)⟩
      have : (∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Mdim k r a - 2))) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
        rw [ha, norm_zero]
        refine zero_pow ?_
        have := a.2
        unfold Mdim
        omega
      rw [this, zero_mul]
    · exact absurd rfl hw

theorem measurable_bcWeight (T T' : ℝ) : Measurable (bcWeight k r T T') := by
  show Measurable fun p : (Fin r → ℂ) × ℂ => if T * T' ≤ Complex.normSq p.2 then
    (∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq p.2 - T * T') ^ (k - 1) else 0
  have hn : Measurable fun p : (Fin r → ℂ) × ℂ => Complex.normSq p.2 :=
    Complex.continuous_normSq.measurable.comp measurable_snd
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const hn
  · first
      | exact (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).comp measurable_fst).norm.pow_const _).mul
          ((hn.sub_const _).pow_const _)
      | fun_prop
      | measurability

theorem measurableSet_Qset (D : RealPlaceData k r Wp Wq) : MeasurableSet (Qset D) := by
  exact measurableSet_lt measurable_const (measurable_bcWeight _ _)

theorem ae_mem_good_set_restrict (D : RealPlaceData k r Wp Wq) : ∀ᵐ q ∂(volume.restrict (Qset D)), q ∈ Q0 D := by
  exact (ae_restrict_iff' (measurableSet_Qset D)).2 ((ae_mem_good_set_or_weight_zero D).mono fun q h hq => h.resolve_right (ne_of_gt hq))

end setting

section fd

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS

theorem properFD (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    ProperSpace W := by
  infer_instance

attribute [local instance] properFD

def piM (D : RealPlaceData k r Wp Wq) : Mt k r → (Wp →L[ℂ] Wp) :=
  {x : Mt k r | Matrix.of x ∈ UWset k r D.z}.indicator fun x => D.π (Matrix.of x)

def piM' (D : RealPlaceData k r Wp Wq) : Mt k r → (Wq →L[ℂ] Wq) :=
  {x : Mt k r | Matrix.of x ∈ UWset k r D.z'}.indicator fun x => D.π' (Matrix.of x)

def FM (F : Mat k r → (Wq →L[ℂ] Wp)) : Mt k r → (Wq →L[ℂ] Wp) :=
  {x : Mt k r | Matrix.of x ∈ GV k r}.indicator fun x => F (Matrix.of x)

theorem sm_piM (D : RealPlaceData k r Wp Wq) : StronglyMeasurable (piM D) := by
  exact sm_ind (isClosed_UW D.z).measurableSet D.π_cont

theorem sm_piM' (D : RealPlaceData k r Wp Wq) : StronglyMeasurable (piM' D) := by
  exact sm_ind (isClosed_UW D.z').measurableSet D.π'_cont

theorem sm_FM {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) : StronglyMeasurable (FM F) := by
  exact sm_ind isClosed_GV.measurableSet hF

theorem FM_eq (F : Mat k r → (Wq →L[ℂ] Wp)) {x : Mt k r} (hx : Matrix.of x ∈ GV k r) :
    FM F x = F (Matrix.of x) := by
  exact Set.indicator_of_mem hx _

theorem piM_eq (D : RealPlaceData k r Wp Wq) {x : Mt k r} (hx : Matrix.of x ∈ UWset k r D.z) :
    piM D x = D.π (Matrix.of x) := by
  exact Set.indicator_of_mem hx _

theorem piM'_eq (D : RealPlaceData k r Wp Wq) {x : Mt k r} (hx : Matrix.of x ∈ UWset k r D.z') :
    piM' D x = D.π' (Matrix.of x) := by
  exact Set.indicator_of_mem hx _

def sgsM (p : SS k r) (x : Mt k r) : Mt k r := sgs p (Matrix.of x)

theorem meas_mulM {α : Type*} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => mulM (f a) (g a) := by
  first
    | exact continuous_mulM.measurable.comp (hf.prodMk hg)
    | exact continuous_mulM.measurable.comp (hf.prod_mk hg)

theorem sgsM_eq (p : SS k r) (x : Mt k r) :
    sgsM p x = mulM (mulM (mulM (mulM (invM p.1.1) (invM p.1.2)) x) p.2.2) p.2.1 := by
  first
    | rfl
    | (simp only [sgsM, sgs, mulM, invM]; rfl)

theorem measurable_sgsM : Measurable fun a : SS k r × Mt k r => sgsM a.1 a.2 := by
  have e : (fun a : SS k r × Mt k r => sgsM a.1 a.2) = fun a =>
      mulM (mulM (mulM (mulM (invM a.1.1.1) (invM a.1.1.2)) a.2) a.1.2.2) a.1.2.1 :=
    funext fun a => sgsM_eq a.1 a.2
  rw [e]
  exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_fst.fst.fst)
    (measurable_invM.comp measurable_fst.fst.snd)) measurable_snd) measurable_fst.snd.snd) measurable_fst.snd.fst

def RM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (x : Mt k r) : Wq →L[ℂ] Wp :=
  (piM D p.1.1).comp ((FM F (sgsM p x)).comp (piM' D (invM p.2.1)))

theorem sm_RM (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : SS k r × Mt k r => RM D F a.1 a.2 := by
  have f1 : StronglyMeasurable fun a : SS k r × Mt k r => piM D a.1.1.1 :=
    (sm_piM D).comp_measurable measurable_fst.fst.fst
  have f2 : StronglyMeasurable fun a : SS k r × Mt k r => FM F (sgsM a.1 a.2) :=
    (sm_FM hF).comp_measurable measurable_sgsM
  have f3 : StronglyMeasurable fun a : SS k r × Mt k r => piM' D (invM a.1.2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp measurable_fst.snd.fst)
  show StronglyMeasurable fun a : SS k r × Mt k r => (piM D a.1.1.1).comp ((FM F (sgsM a.1 a.2)).comp (piM' D (invM a.1.2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))

theorem RM_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    {x : Mt k r} (hx : Matrix.of x ∈ GV k r) : RM D F p x = rho D p F (Matrix.of x) := by
  rw [RM, piM_eq D (x := p.1.1) hp.1, FM_eq F (x := sgsM p x) (sgs_mem D hp hx),
    piM'_eq D (x := invM p.2.1) (WeylGroupFacts.uw_inv hp.2.2.1)]
  try rfl

def hsL : (Wq →L[ℂ] Wp) →L[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  LinearMap.toContinuousLinearMap
    { toFun := hsVec
      map_add' := fun A B => by ext i; simp [hsVec]
      map_smul' := fun a A => by ext i; simp [hsVec] }

theorem hsL_apply (A : Wq →L[ℂ] Wp) : hsL A = hsVec A := rfl

theorem measurable_xi (D : RealPlaceData k r Wp Wq) : Measurable fun a : (ℝ × ℝ) × SS k r => xiTau D a.1 a.2 := by
  have h : Measurable fun a : (ℝ × ℝ) × SS k r =>
      (a.1.1 * lam k r D.z (Matrix.of a.2.1.2) - a.1.2 * lam k r D.z' (Matrix.of a.2.2.2)) :=
    (measurable_fst.fst.mul ((continuous_lam D.z).measurable.comp measurable_snd.fst.snd)).sub
      (measurable_fst.snd.mul ((continuous_lam D.z').measurable.comp measurable_snd.snd.snd))
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h))

def JM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : (Fin r → ℂ) × ℂ) :
    Wq →L[ℂ] Wp := ∫ p, xiTau D τ p • RM D F p (gqM D q) ∂D.μSS

set_option maxHeartbeats 800000 in

theorem sm_A (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => RM D F b.2 (gqM D b.1.2) := by
  have hm : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => gqM D b.1.2 :=
    (measurable_gqM D).comp measurable_fst.snd
  have f1 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => piM D b.2.1.1 :=
    (sm_piM D).comp_measurable measurable_snd.fst.fst
  have hs : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => sgsM b.2 (gqM D b.1.2) := by
    have e : (fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => sgsM b.2 (gqM D b.1.2)) = fun b =>
        mulM (mulM (mulM (mulM (invM b.2.1.1) (invM b.2.1.2)) (gqM D b.1.2)) b.2.2.2) b.2.2.1 :=
      funext fun b => sgsM_eq b.2 (gqM D b.1.2)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
      (measurable_invM.comp measurable_snd.fst.snd)) hm) measurable_snd.snd.snd) measurable_snd.snd.fst
  have f2 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => FM F (sgsM b.2 (gqM D b.1.2)) :=
    (sm_FM hF).comp_measurable hs
  have f3 : StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => piM' D (invM b.2.2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp measurable_snd.snd.fst)
  show StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r =>
    (piM D b.2.1.1).comp ((FM F (sgsM b.2 (gqM D b.1.2))).comp (piM' D (invM b.2.2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))

theorem sm_B (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r =>
      xiTau D b.1.1 b.2 • RM D F b.2 (gqM D b.1.2) := by
  have hx : Measurable fun b : ((ℝ × ℝ) × ((Fin r → ℂ) × ℂ)) × SS k r => xiTau D b.1.1 b.2 := by
    first
      | exact (measurable_xi D).comp (measurable_fst.fst.prodMk measurable_snd)
      | exact (measurable_xi D).comp (measurable_fst.fst.prod_mk measurable_snd)
  exact hx.stronglyMeasurable.smul (sm_A D hF)

theorem sm_JM (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : (ℝ × ℝ) × ((Fin r → ℂ) × ℂ) => JM D F a.1 a.2 := by
  first
    | exact (sm_B D hF).integral_prod_right'
    | exact (sm_B D hF).integral_prod_right

theorem ae_RM_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) :
    ∀ᵐ p ∂D.μSS, RM D F p (gqM D q) = rho D p F (gq D q) := by
  filter_upwards [ae_inSS D] with p hp
  rw [gqM_eq D hq]
  exact RM_eq D F hp (gq_mem D hq)

theorem JM_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ Q0 D) : JM D F τ q = Jtau D τ F (gq D q) := by
  rw [JM, Jtau]
  refine integral_congr_ae ?_
  filter_upwards [ae_RM_eq D F hq] with p hp
  rw [hp]

def KM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (p : SS k r) (x : Mt k r) : ℂ :=
  hsInner (RM D F p x) (FM F x)

def Om (D : RealPlaceData k r Wp Wq) (w₁ w₂ : ℝ → ℝ) (p : SS k r) : ℂ :=
  om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2))

def PhiM (D : RealPlaceData k r Wp Wq) (a : ((Fin r → ℂ) × ℂ) × SS k r) : Mt k r := sgsM a.2 (gqM D a.1)

def nuQ (D : RealPlaceData k r Wp Wq) : Measure ((Fin r → ℂ) × ℂ) :=
  volume.withDensity fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q)

def GM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (w₁ w₂ : ℝ → ℝ) (x : Mt k r) : ℂ :=
  ∫ p, Om D w₁ w₂ p * KM D F p x ∂D.μSS

def tr (p' p : SS k r) : SS k r :=
  ((lmulM (Matrix.of p'.1.1) p.1.1, lmulM (Matrix.of p'.1.2) (conjM (Matrix.of p'.1.1) p.1.2)),
   (lmulM (Matrix.of p'.2.1) p.2.1, lmulM (Matrix.of p'.2.2) (conjM (Matrix.of p'.2.1) p.2.2)))

end fd

section dil

variable {k r : ℕ}

theorem d_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  exact sf h

def d_dg (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)

theorem d_aDil_eq (t : ℝ) : aDil k r t = Matrix.diagonal (d_dg k r t) := rfl

theorem d_isUnit_aDil (t : ℝ) (ht : t ≠ 0) : IsUnit (aDil k r t).det := by
  rw [d_aDil_eq, Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  unfold d_dg
  split_ifs <;> simp [ht]

theorem d_comm (z : Fin (2 * r + k + 1) → ℂ) (t : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    aDil k r t * h = h * aDil k r t := by
  have hb := WeylGroupFacts.uw_block hh
  ext i j
  rw [d_aDil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [hb.2 i j hi]
    by_cases hij : i = j
    · subst hij; simp [mul_comm]
    · simp [hij]
  · by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hb.1 i j hj]
      by_cases hij : i = j
      · subst hij; simp [mul_comm]
      · simp [hij]
    · have e1 : d_dg k r t i = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      have e2 : d_dg k r t j = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      rw [e1, e2, one_mul, mul_one]

theorem d_conj_apply (t : ℝ) (ht : t ≠ 0) (n : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (aDil k r t * n * (aDil k r t)⁻¹) i j = d_dg k r t i * n i j * d_dg k r t⁻¹ j := by
  rw [Formalism.FourierDecayAlt.P.B2.aDil_inv k r t ht, d_aDil_eq, d_aDil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem d_ell (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (t : ℝ) (ht : t ≠ 0) (n : Mat k r) :
    ell k r z (aDil k r t * n * (aDil k r t)⁻¹) = (t : ℂ) * ell k r z n := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha := a.isLt
  by_cases h : a.val + 1 < r
  · rw [dif_pos h, dif_pos h, d_conj_apply t ht]
    have e1 : d_dg k r t (eI k r a) = ((t ^ (r - a.val) : ℝ) : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]; rfl
    have e2 : d_dg k r t⁻¹ (eI k r ⟨a.val + 1, h⟩) = (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]; rfl
    rw [e1, e2]
    have e3 : r - a.val = (r - (a.val + 1)) + 1 := by omega
    have e4 : ((t ^ (r - a.val) : ℝ) : ℂ) * (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_mul, e3, pow_succ, mul_assoc, mul_comm t, ← mul_assoc, ← mul_pow,
        mul_inv_cancel₀ ht, one_pow, one_mul]
    calc _ = (((t ^ (r - a.val) : ℝ) : ℂ) * (((t⁻¹) ^ (r - (a.val + 1)) : ℝ) : ℂ)) *
          n (eI k r a) (eI k r ⟨a.val + 1, h⟩) := by ring
      _ = _ := by rw [e4]
  · rw [dif_neg h, dif_neg h]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [d_conj_apply t ht]
    have e1 : d_dg k r t (eI k r a) = (t : ℂ) := by
      unfold d_dg; rw [if_pos (by simp only [eI]; omega)]
      have : r - (eI k r a).val = 1 := by simp only [eI]; omega
      rw [this, pow_one]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj]; simp
    · have e2 : d_dg k r t⁻¹ j = 1 := by
        unfold d_dg; rw [if_neg (by omega), if_pos (by omega)]
      rw [e1, e2]; ring

theorem d_lam (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (t : ℝ) (ht : t ≠ 0) (n : Mat k r) :
    lam k r z (aDil k r t * n * (aDil k r t)⁻¹) = t * lam k r z n := by
  unfold lam
  rw [d_ell z hz t ht, ← mul_assoc, mul_comm cStd, mul_assoc, Complex.re_ofReal_mul]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem d_ae_uw (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ UWset k r D.z ∧ Matrix.of p.2.1 ∈ UWset k r D.z' := by
  exact (ae_inSS D).mono fun p hp => ⟨hp.1, hp.2.2.1⟩

def d_dilE (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) : SS k r ≃ᵐ SS k r :=
  ((MeasurableEquiv.refl _).prodCongr (BesselUnitaryEquiv.conjE (aDil k r t.1) (d_isUnit_aDil t.1 h1))).prodCongr
    ((MeasurableEquiv.refl _).prodCongr (BesselUnitaryEquiv.conjE (aDil k r t.2) (d_isUnit_aDil t.2 h2)))

theorem d_dilE_apply (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (p : SS k r) :
    d_dilE t h1 h2 p = dilation₂ t p := rfl

theorem d_map_dil (D : RealPlaceData k r Wp Wq) (hJ : DilJac D) (t : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2) :
    D.μSS.map (d_dilE t h1.ne' h2.ne') =
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)) • D.μSS := by
  have := d_sf D.haarW
  have := d_sf D.haarW'
  have := d_sf D.haarN
  have e : ⇑(d_dilE (k := k) (r := r) t h1.ne' h2.ne') =
      Prod.map (Prod.map id (conjM (aDil k r t.1))) (Prod.map id (conjM (aDil k r t.2))) := rfl
  have m1 : Measurable (conjM (aDil k r t.1)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  have m2 : Measurable (conjM (aDil k r t.2)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  rw [e]
  unfold RealPlaceData.μSS
  rw [← Measure.map_prod_map _ _ (measurable_id.prodMap m1) (measurable_id.prodMap m2),
    ← Measure.map_prod_map _ _ measurable_id m1, ← Measure.map_prod_map _ _ measurable_id m2,
    hJ t.1 h1, hJ t.2 h2, Measure.map_id, Measure.map_id, Measure.prod_smul_right, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_smul_left, smul_smul,
    mul_comm (ENNReal.ofReal ((t.2 ^ kap k r)⁻¹))]

theorem d_xi (D : RealPlaceData k r Wp Wq) (τ t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (p : SS k r) :
    xiTau D τ (dilation₂ t p) = xiTau D (τ.1 * t.1, τ.2 * t.2) p := by
  unfold xiTau dilation₂
  have e1 : lam k r D.z (Matrix.of (conjM (aDil k r t.1) p.1.2)) = t.1 * lam k r D.z (Matrix.of p.1.2) :=
    d_lam D.z D.z_mem t.1 h1 _
  have e2 : lam k r D.z' (Matrix.of (conjM (aDil k r t.2) p.2.2)) = t.2 * lam k r D.z' (Matrix.of p.2.2) :=
    d_lam D.z' D.z'_mem t.2 h2 _
  simp only [e1, e2, mul_assoc]

theorem d_rho (D : RealPlaceData k r Wp Wq) (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) (p : SS k r)
    (hp : Matrix.of p.1.1 ∈ UWset k r D.z) (hp' : Matrix.of p.2.1 ∈ UWset k r D.z') :
    rho D (dilation₂ t p) (dilF t F) g = rho D p F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  obtain ⟨⟨h, m⟩, ⟨h', m'⟩⟩ := p
  set H : Mat k r := Matrix.of h
  set M : Mat k r := Matrix.of m
  set H' : Mat k r := Matrix.of h'
  set M' : Mat k r := Matrix.of m'
  set a₁ := aDil k r t.1
  set a₂ := aDil k r t.2
  have u1 : IsUnit a₁.det := d_isUnit_aDil t.1 h1
  have u2 : IsUnit a₂.det := d_isUnit_aDil t.2 h2
  have c1 : a₁ * H⁻¹ = H⁻¹ * a₁ := d_comm D.z t.1 (WeylGroupFacts.uw_inv hp)
  have c2 : a₂ * H' = H' * a₂ := d_comm D.z' t.2 hp'
  have c1' : a₁⁻¹ * H⁻¹ = H⁻¹ * a₁⁻¹ := by
    calc a₁⁻¹ * H⁻¹ = a₁⁻¹ * (H⁻¹ * a₁) * a₁⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ u1, Matrix.mul_one]
      _ = a₁⁻¹ * (a₁ * H⁻¹) * a₁⁻¹ := by rw [c1]
      _ = H⁻¹ * a₁⁻¹ := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ u1]
  have key : a₁⁻¹ * (H⁻¹ * (a₁ * M * a₁⁻¹)⁻¹ * g * (a₂ * M' * a₂⁻¹) * H') * a₂ =
      H⁻¹ * M⁻¹ * (a₁⁻¹ * g * a₂) * M' * H' := by
    have i1 : (a₁ * M * a₁⁻¹)⁻¹ = a₁ * M⁻¹ * a₁⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u1, Matrix.mul_assoc]
    rw [i1]
    calc a₁⁻¹ * (H⁻¹ * (a₁ * M⁻¹ * a₁⁻¹) * g * (a₂ * M' * a₂⁻¹) * H') * a₂
        = (a₁⁻¹ * H⁻¹) * a₁ * M⁻¹ * a₁⁻¹ * g * a₂ * M' * a₂⁻¹ * (H' * a₂) := by
          simp only [Matrix.mul_assoc]
      _ = H⁻¹ * (a₁⁻¹ * a₁) * M⁻¹ * a₁⁻¹ * g * a₂ * M' * (a₂⁻¹ * a₂) * H' := by
          rw [c1', ← c2]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [Matrix.nonsing_inv_mul _ u1, Matrix.nonsing_inv_mul _ u2]
          simp only [Matrix.mul_assoc, Matrix.mul_one]
  show (D.π H).comp ((F (a₁⁻¹ * (H⁻¹ * (a₁ * M * a₁⁻¹)⁻¹ * g * (a₂ * M' * a₂⁻¹) * H') * a₂)).comp (D.π' H'⁻¹)) =
    (D.π H).comp ((F (H⁻¹ * M⁻¹ * (a₁⁻¹ * g * a₂) * M' * H')).comp (D.π' H'⁻¹))
  rw [key]

theorem d_Jtau (D : RealPlaceData k r Wp Wq) (hJ : DilJac D) (τ t : ℝ × ℝ) (h1 : 0 < t.1) (h2 : 0 < t.2)
    (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r) :
    Jtau D τ (dilF t F) g = ((t.1 * t.2) ^ kap k r : ℝ) •
      Jtau D (τ.1 * t.1, τ.2 * t.2) F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) := by
  have hc : ((t.1 * t.2) ^ kap k r : ℝ) ≠ 0 := (pow_pos (mul_pos h1 h2) _).ne'
  have hm := d_map_dil D hJ t h1 h2
  have e1 : (∫ p, xiTau D τ p • rho D p (dilF t F) g ∂(D.μSS.map (d_dilE t h1.ne' h2.ne'))) =
      ∫ p, xiTau D (τ.1 * t.1, τ.2 * t.2) p • rho D p F ((aDil k r t.1)⁻¹ * g * aDil k r t.2) ∂D.μSS := by
    rw [integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [d_ae_uw D] with p hp
    rw [d_dilE_apply, d_xi D τ t h1.ne' h2.ne', d_rho D t h1.ne' h2.ne' F g p hp.1 hp.2]
  unfold Jtau
  rw [← e1, hm, integral_smul_measure, smul_smul]
  have : ((t.1 * t.2) ^ kap k r : ℝ) *
      (ENNReal.ofReal ((t.1 ^ kap k r)⁻¹) * ENNReal.ofReal ((t.2 ^ kap k r)⁻¹)).toReal = 1 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
      mul_pow]
    field_simp
  rw [this, one_smul]

def d_S (r : ℕ) (s : ℝ) (q : (Fin r → ℂ) × ℂ) : (Fin r → ℂ) × ℂ :=
  (fun a => ((s ^ (r - a.val) : ℝ) : ℂ) * q.1 a, q.2)

theorem d_gq (D : RealPlaceData k r Wp Wq) (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (q : (Fin r → ℂ) × ℂ) :
    (aDil k r t.1)⁻¹ * gq D q * aDil k r t.2 = gq D (d_S r (t.1 * t.2) q) :=
  Formalism.FourierDecayAlt.P.dilation_big_cell_formula k r q.1 (D.μsec q.2) t.1 t.2 h1 h2

def halfDimensionBlockSummand (k r : ℕ) : ℕ := ∑ a : Fin r, (r - a.val) * (2 * (Mdim k r a - 2))

def halfDimensionRankTwoSummand (r : ℕ) : ℕ := ∑ a : Fin r, (r - a.val) * 2

theorem d_kap (k r : ℕ) : kap k r = halfDimensionBlockSummand k r + halfDimensionRankTwoSummand r := by
  unfold kap halfDimensionBlockSummand halfDimensionRankTwoSummand
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have : Mdim k r a = (Mdim k r a - 2) + 2 := by
    have := a.isLt
    unfold Mdim; omega
  have e : Mdim k r a - 1 = (Mdim k r a - 2) + 1 := by omega
  rw [e]; ring

theorem d_weight (T T' s : ℝ) (hs : 0 < s) (q : (Fin r → ℂ) × ℂ) :
    bcWeight k r T T' (d_S r s q) = s ^ halfDimensionBlockSummand k r * bcWeight k r T T' q := by
  unfold bcWeight d_S
  dsimp only
  split_ifs with h
  · rw [← mul_assoc]
    congr 1
    rw [halfDimensionBlockSummand, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hs _), ← pow_mul]
  · simp

theorem d_pi_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → NNReal) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  refine Measure.pi_eq fun s _ => ?_
  first
    | simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
        Finset.prod_mul_distrib]
    | simp [Finset.prod_mul_distrib]

theorem d_map_mul (ρ : ℝ) (hρ : 0 < ρ) :
    (volume : Measure ℂ).map (fun x => (ρ : ℂ) * x) = (Real.toNNReal ((ρ ^ 2)⁻¹)) • (volume : Measure ℂ) := by
  have h := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
  rw [Complex.finrank_real_complex, abs_of_pos (by positivity)] at h
  have e : (fun x : ℂ => (ρ : ℂ) * x) = (ρ • ·) := by funext x; rw [Complex.real_smul]
  rw [e, h]; rfl

theorem map_volume_triangular_scaling (s : ℝ) (hs : 0 < s) :
    (volume : Measure (Fin r → ℂ)).map (fun c a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) =
      (∏ a : Fin r, Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) • (volume : Measure (Fin r → ℂ)) := by
  have h := measurePreserving_pi (fun _ : Fin r => (volume : Measure ℂ))
    (fun a : Fin r => (Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) • (volume : Measure ℂ))
    (f := fun a x => ((s ^ (r - a.val) : ℝ) : ℂ) * x)
    (fun a => ⟨(continuous_const.mul continuous_id).measurable, d_map_mul _ (by positivity)⟩)
  rw [volume_pi, h.map_eq, d_pi_smul]

theorem d_map_S (s : ℝ) (hs : 0 < s) :
    (volume : Measure ((Fin r → ℂ) × ℂ)).map (d_S r s) =
      ENNReal.ofReal ((s ^ halfDimensionRankTwoSummand r)⁻¹) • (volume : Measure ((Fin r → ℂ) × ℂ)) := by
  have e : d_S r s = Prod.map (fun (c : Fin r → ℂ) a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) id := rfl
  have m1 : Measurable (fun (c : Fin r → ℂ) a => ((s ^ (r - a.val) : ℝ) : ℂ) * c a) :=
    measurable_pi_iff.2 fun a => (continuous_const.mul (continuous_apply a)).measurable
  have hc : (∏ a : Fin r, Real.toNNReal (((s ^ (r - a.val)) ^ 2)⁻¹)) = Real.toNNReal ((s ^ halfDimensionRankTwoSummand r)⁻¹) := by
    rw [← Real.toNNReal_prod_of_nonneg (fun a _ => by positivity)]
    congr 1
    unfold halfDimensionRankTwoSummand
    rw [Finset.prod_inv_distrib, ← Finset.prod_pow_eq_pow_sum]
    simp only [pow_mul]
  rw [e, Measure.volume_eq_prod, ← Measure.map_prod_map _ _ m1 measurable_id, map_volume_triangular_scaling s hs, Measure.map_id,
    Measure.prod_smul_left, hc]
  rfl

theorem d_emb_S (s : ℝ) (hs : 0 < s) : MeasurableEmbedding (d_S r s) := by
  have hs0 : s ≠ 0 := hs.ne'
  have hm : ∀ u : ℝ, Measurable (d_S r u) := fun u => by
    show Measurable fun q : (Fin r → ℂ) × ℂ => ((fun a : Fin r => ((u ^ (r - a.val) : ℝ) : ℂ) * q.1 a), q.2)
    first
      | fun_prop
      | exact (by fun_prop : Continuous fun q : (Fin r → ℂ) × ℂ => ((fun a : Fin r => ((u ^ (r - a.val) : ℝ) : ℂ) * q.1 a), q.2)).measurable
      | measurability
  have key : ∀ (u v : ℝ), u * v = 1 → ∀ q, d_S r u (d_S r v q) = q := by
    intro u v huv q
    refine Prod.ext (funext fun a => ?_) rfl
    show ((u ^ (r - a.val) : ℝ) : ℂ) * (((v ^ (r - a.val) : ℝ) : ℂ) * q.1 a) = q.1 a
    rw [← mul_assoc, ← Complex.ofReal_mul, ← mul_pow, huv, one_pow, Complex.ofReal_one, one_mul]
  refine MeasurableEmbedding.of_measurable_inverse (hm s) ?_ (hm s⁻¹) (key s⁻¹ s (inv_mul_cancel₀ hs0))
  have : Set.range (d_S r s) = Set.univ := Set.eq_univ_of_forall fun q => ⟨_, key s s⁻¹ (mul_inv_cancel₀ hs0) q⟩
  rw [this]
  exact MeasurableSet.univ

theorem d_hsVec_smul [FiniteDimensional ℂ Wq] (x : ℝ) (A : Wq →L[ℂ] Wp) :
    ‖hsVec (x • A)‖ = |x| * ‖hsVec A‖ := by
  have e : hsVec (x • A) = x • hsVec A := by
    first
      | (ext i; simp [hsVec])
      | (unfold hsVec; rw [← WithLp.toLp_smul]; congr 1; funext i; simp)
  rw [e, norm_smul, Real.norm_eq_abs]

theorem d_stepDilBeta : Formalism.FourierDecayAlt.B.StepDilBeta := by
  intro k r Wp Wq _ _ _ _ _ _ D A hJ F _ τ _ t ht
  have h1 : 0 < t.1 := ht.1
  have h2 : 0 < t.2 := ht.2
  set s : ℝ := t.1 * t.2 with hs_def
  have hs : 0 < s := mul_pos h1 h2
  set T := Tz k r D.z
  set T' := Tz k r D.z'
  set f : (Fin r → ℂ) × ℂ → ℝ≥0∞ := fun q =>
    ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D (τ.1 * t.1, τ.2 * t.2) F (gq D q))‖ ^ 2) with hf
  have hpt : ∀ q, ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D τ (dilF t F) (gq D q))‖ ^ 2) =
      ENNReal.ofReal ((s ^ kap k r) ^ 2 * (s ^ halfDimensionBlockSummand k r)⁻¹) * f (d_S r s q) := by
    intro q
    rw [d_Jtau D hJ τ t h1 h2 F (gq D q), d_gq D t h1.ne' h2.ne' q, d_hsVec_smul, hf]
    simp only
    rw [d_weight T T' s hs q, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity)]
    congr 1
    field_simp
    rfl
  show (∫⁻ q, ENNReal.ofReal (bcWeight k r T T' q * ‖hsVec (Jtau D τ (dilF t F) (gq D q))‖ ^ 2)) =
    ENNReal.ofReal (s ^ kap k r) * ∫⁻ q, f q
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← (d_emb_S s hs).lintegral_map, d_map_S s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [d_kap]
  field_simp
  ring

end dil

section jc

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS properFD

theorem jc_ae_FM (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) :
    ∀ᵐ g ∂D.μG, FM F g = F (Matrix.of g) := by
  exact (ae_mem D.haarG).mono fun g hg => FM_eq F hg

theorem jc_aesm_F (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
  exact (sm_FM hF).aestronglyMeasurable.congr (jc_ae_FM D F)

theorem jc_cont {A : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) : ContinuousOn F (GV k r) := by
  obtain ⟨c, h, _⟩ := hF
  exact contOn_of_CkOn h

theorem jc_bound {A : ℝ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∃ c, ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c := by
  obtain ⟨c, _, h⟩ := hF
  exact ⟨c, fun g hg => h [] [] (by simp) (by simp) (by simp) g hg⟩

theorem jc_lint (D : RealPlaceData k r Wp Wq) {A : ℝ} (hCC : CCIntegrable D A) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : InCC A 4 F) : (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) < ∞ := by
  obtain ⟨c, hc⟩ := jc_bound hF
  have h := hCC F c (jc_aesm_F D (jc_cont hF)) hc
  have e : (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) = ∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂D.μG := by
    refine lintegral_congr_ae ?_
    filter_upwards [jc_ae_FM D F] with g hg
    rw [hg]
  rw [e]
  exact h

def jc_E (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) : ℝ≥0∞ :=
  ∫⁻ p, ‖FM F (sgsM p (gqM D q))‖ₑ ∂D.μSS

theorem jc_sm_FPhi (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => FM F (sgsM a.2 (gqM D a.1)) := by
  have hs : Measurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => sgsM a.2 (gqM D a.1) := by
    have e : (fun a : ((Fin r → ℂ) × ℂ) × SS k r => sgsM a.2 (gqM D a.1)) = fun a =>
        mulM (mulM (mulM (mulM (invM a.2.1.1) (invM a.2.1.2)) (gqM D a.1)) a.2.2.2) a.2.2.1 :=
      funext fun a => sgsM_eq a.2 (gqM D a.1)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
      (measurable_invM.comp measurable_snd.fst.snd)) ((measurable_gqM D).comp measurable_fst))
      measurable_snd.snd.snd) measurable_snd.snd.fst
  have f2 : StronglyMeasurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => FM F (sgsM a.2 (gqM D a.1)) :=
    (sm_FM hF).comp_measurable hs
  exact f2

theorem jc_meas_E (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    Measurable (jc_E D F) := by
  show Measurable fun q => ∫⁻ p, ‖FM F (sgsM p (gqM D q))‖ₑ ∂D.μSS
  first
    | exact (jc_sm_FPhi D hF).enorm.lintegral_prod_right'
    | exact (jc_sm_FPhi D hF).ennnorm.lintegral_prod_right'
    | exact (jc_sm_FPhi D hF).measurable.enorm.lintegral_prod_right'

theorem jc_formula (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) :
    (∫⁻ g, ‖FM F g‖ₑ ∂D.μG) = ∫⁻ q : (Fin r → ℂ) × ℂ,
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * jc_E D F q := by
  have hf : Measurable fun x : Mt k r => ‖FM F x‖ₑ := (sm_FM hF).enorm
  rw [hI _ hf]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · unfold jc_E
    rw [gqM_eq D h]
    rfl
  · rw [h]
    simp

theorem jc_ae_E (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ᵐ q ∂(volume.restrict (Qset D)), jc_E D F q < ∞ := by
  have hc := jc_cont hF
  have h1 := jc_lint D hCC hF
  rw [jc_formula D hI hc] at h1
  have hm : Measurable fun q : (Fin r → ℂ) × ℂ =>
      ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) * jc_E D F q :=
    (ENNReal.measurable_ofReal.comp (measurable_bcWeight _ _)).mul (jc_meas_E D hc)
  have h2 := ae_lt_top hm h1.ne
  rw [ae_restrict_iff' (measurableSet_Qset D)]
  filter_upwards [h2] with q hq hqQ
  by_contra hcon
  have htop : jc_E D F q = ∞ := not_lt_top_iff.1 hcon
  rw [htop, ENNReal.mul_top] at hq
  · exact lt_irrefl _ hq
  · have : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hqQ
    simpa using this

private theorem stronglyMeasurable_rm_comp (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    {α : Type*} [MeasurableSpace α] {φ : α → SS k r} {ψ : α → Mt k r} (hφ : Measurable φ) (hψ : Measurable ψ) :
    StronglyMeasurable fun a => RM D F (φ a) (ψ a) := by
  have f1 : StronglyMeasurable fun a => piM D (φ a).1.1 := (sm_piM D).comp_measurable hφ.fst.fst
  have hs : Measurable fun a => sgsM (φ a) (ψ a) := by
    have e : (fun a => sgsM (φ a) (ψ a)) = fun a =>
        mulM (mulM (mulM (mulM (invM (φ a).1.1) (invM (φ a).1.2)) (ψ a)) (φ a).2.2) (φ a).2.1 :=
      funext fun a => sgsM_eq (φ a) (ψ a)
    rw [e]
    exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp hφ.fst.fst)
      (measurable_invM.comp hφ.fst.snd)) hψ) hφ.snd.snd) hφ.snd.fst
  have f2 : StronglyMeasurable fun a => FM F (sgsM (φ a) (ψ a)) := (sm_FM hF).comp_measurable hs
  have f3 : StronglyMeasurable fun a => piM' D (invM (φ a).2.1) :=
    (sm_piM' D).comp_measurable (measurable_invM.comp hφ.snd.fst)
  show StronglyMeasurable fun a => (piM D (φ a).1.1).comp ((FM F (sgsM (φ a) (ψ a))).comp (piM' D (invM (φ a).2.1)))
  first
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prodMk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prodMk f3)))
    | exact isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable
        (f1.prod_mk (isBoundedBilinearMap_comp.continuous.comp_stronglyMeasurable (f2.prod_mk f3)))

theorem jc_integrable_of (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) (hE : jc_E D F q < ∞) :
    Integrable (fun p => rho D p F (gq D q)) D.μSS := by
  have hsm : StronglyMeasurable fun p : SS k r => RM D F p (gqM D q) :=
    stronglyMeasurable_rm_comp D hF measurable_id measurable_const
  refine ⟨hsm.aestronglyMeasurable.congr (ae_RM_eq D F hq), ?_⟩
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hE
  filter_upwards [ae_inSS D] with p hp
  have hg : gq D q ∈ GV k r := gq_mem D hq
  have h1 : ‖rho D p F (gq D q)‖ₑ ≤ ‖F (sgs p (gq D q))‖ₑ := by
    first
      | exact enorm_le_iff_norm_le.2 (norm_rho_le D hp F _)
      | exact ENNReal.coe_le_coe.2 (norm_rho_le D hp F _)
  have h2 : FM F (sgsM p (gqM D q)) = F (sgs p (gq D q)) := by
    rw [gqM_eq D hq]
    exact FM_eq F (x := sgsM p (gq D q)) (sgs_mem D hp hg)
  rw [h2]
  exact h1

theorem jc_ae_integrable (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∀ᵐ q ∂(volume.restrict (Qset D)), Integrable (fun p => rho D p F (gq D q)) D.μSS := by
  filter_upwards [jc_ae_E D hI hCC hF, ae_mem_good_set_restrict D] with q hE hq
  exact jc_integrable_of D (jc_cont hF) hq hE

theorem jc_cont_tau (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (h : Integrable (fun p => rho D p F g) D.μSS) : Continuous fun τ => Jtau D τ F g := by
  show Continuous fun τ => ∫ p, xiTau D τ p • rho D p F g ∂D.μSS
  have hxm : ∀ τ : ℝ × ℝ, Measurable fun p : SS k r => xiTau D τ p := fun τ => by
    first
      | exact (measurable_xi D).comp (measurable_const.prodMk measurable_id)
      | exact (measurable_xi D).comp (measurable_const.prod_mk measurable_id)
  refine continuous_of_dominated (bound := fun p => ‖rho D p F g‖) (fun τ => ?_)
    (fun τ => ae_of_all _ fun p => ?_) h.norm (ae_of_all _ fun p => ?_)
  · exact (hxm τ).aestronglyMeasurable.smul h.aestronglyMeasurable
  · simp [norm_smul, norm_xi]
  · first
      | exact ((continuous_xi D).comp (continuous_id.prodMk continuous_const)).smul continuous_const
      | exact ((continuous_xi D).comp (continuous_id.prod_mk continuous_const)).smul continuous_const

theorem jc_aesm_J (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    (τ : ℝ × ℝ) : AEStronglyMeasurable (fun q => Jtau D τ F (gq D q)) (volume.restrict (Qset D)) := by
  have hx : Measurable fun b : ((Fin r → ℂ) × ℂ) × SS k r => xiTau D τ b.2 := by
    first
      | exact (measurable_xi D).comp (measurable_const.prodMk measurable_snd)
      | exact (measurable_xi D).comp (measurable_const.prod_mk measurable_snd)
  have hb : StronglyMeasurable fun b : ((Fin r → ℂ) × ℂ) × SS k r => xiTau D τ b.2 • RM D F b.2 (gqM D b.1) :=
    hx.stronglyMeasurable.smul (stronglyMeasurable_rm_comp D hF measurable_snd ((measurable_gqM D).comp measurable_fst))
  have hs : StronglyMeasurable fun q => JM D F τ q := hb.integral_prod_right'
  refine hs.aestronglyMeasurable.congr ?_
  filter_upwards [ae_mem_good_set_restrict D] with q hq
  exact JM_eq D F τ hq

end jc

theorem jc_stepJCont : Formalism.FourierDecayAlt.B.StepJCont := by
  intro k r Wp Wq _ _ _ _ _ _ D A hI hCC F hF
  refine ⟨jc_ae_integrable D hI hCC hF, ?_, ?_⟩
  · filter_upwards [jc_ae_integrable D hI hCC hF] with q hq
    exact (jc_cont_tau D F _ hq).continuousOn
  · intro τ _
    exact jc_aesm_J D (jc_cont hF) τ

section alg

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS properFD

theorem al_tr_eq (p' : SS k r) : tr p' =
    Prod.map (Prod.map (lmulM (Matrix.of p'.1.1)) (lmulM (Matrix.of p'.1.2) ∘ conjM (Matrix.of p'.1.1)))
      (Prod.map (lmulM (Matrix.of p'.2.1)) (lmulM (Matrix.of p'.2.2) ∘ conjM (Matrix.of p'.2.1))) := rfl

theorem tr_mp (D : RealPlaceData k r Wp Wq) (hC : ConjInv D) {p' : SS k r} (hp' : D.inSS p') :
    MeasurePreserving (tr p') D.μSS D.μSS := by
  rw [al_tr_eq]
  unfold RealPlaceData.μSS
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  refine MeasurePreserving.prod (MeasurePreserving.prod ?_ ?_) (MeasurePreserving.prod ?_ ?_)
  · exact ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarW.left _ h1⟩
  · exact MeasurePreserving.comp ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarN.left _ h2⟩
      ⟨(BesselUnitaryEquiv.continuous_conjM _).measurable, hC _ (Or.inl h1)⟩
  · exact ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarW'.left _ h3⟩
  · exact MeasurePreserving.comp ⟨(BesselUnitaryEquiv.continuous_lmulM _).measurable, D.haarN.left _ h4⟩
      ⟨(BesselUnitaryEquiv.continuous_conjM _).measurable, hC _ (Or.inr h3)⟩

theorem tr_emb (D : RealPlaceData k r Wp Wq) {p' : SS k r} (hp' : D.inSS p') :
    MeasurableEmbedding (tr (k := k) (r := r) p') := by
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  have u1 := WeylGroupFacts.isUnit_of_uh h1.1
  have u2 := WeylGroupFacts.isUnit_of_uh h2.1
  have u3 := WeylGroupFacts.isUnit_of_uh h3.1
  have u4 := WeylGroupFacts.isUnit_of_uh h4.1
  let Φ : SS k r ≃ᵐ SS k r :=
    ((BesselUnitaryEquiv.lmulE _ u1).prodCongr ((BesselUnitaryEquiv.conjE _ u1).trans (BesselUnitaryEquiv.lmulE _ u2))).prodCongr
      ((BesselUnitaryEquiv.lmulE _ u3).prodCongr ((BesselUnitaryEquiv.conjE _ u3).trans (BesselUnitaryEquiv.lmulE _ u4)))
  exact Φ.measurableEmbedding

theorem al_lam_tr (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) {h n₁ n : Mat k r} (hh : h ∈ UWset k r z)
    (hn₁ : n₁ ∈ Nset k r) (hn : n ∈ Nset k r) :
    lam k r z (n₁ * (h * n * h⁻¹)) = lam k r z n₁ + lam k r z n := by
  have hc := unitary_weyl_normal_holds k r z hz h hh n hn
  unfold lam
  rw [length_additive_holds k r z hz n₁ hn₁ _ hc.1, hc.2, mul_add, Complex.add_re]

theorem xi_tr (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) {p' p : SS k r} (hp' : D.inSS p') (hp : D.inSS p) :
    xiTau D τ (tr p' p) = xiTau D τ p' * xiTau D τ p := by
  obtain ⟨a1, a2, a3, a4⟩ := hp'
  obtain ⟨b1, b2, b3, b4⟩ := hp
  have e1 : lam k r D.z (Matrix.of (tr p' p).1.2) = lam k r D.z (Matrix.of p'.1.2) + lam k r D.z (Matrix.of p.1.2) :=
    al_lam_tr D.z D.z_mem a1 a2 b2
  have e2 : lam k r D.z' (Matrix.of (tr p' p).2.2) = lam k r D.z' (Matrix.of p'.2.2) + lam k r D.z' (Matrix.of p.2.2) :=
    al_lam_tr D.z' D.z'_mem a3 a4 b4
  unfold xiTau
  rw [e1, e2, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem al_sum_inner (A B : Wq →L[ℂ] Wp) {ι : Type*} [Fintype ι] (c : OrthonormalBasis ι ℂ Wq) :
    ∑ i, inner ℂ (A (c i)) (B (c i)) =
      LinearMap.trace ℂ Wq ((ContinuousLinearMap.adjoint A).comp B).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ c]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]

theorem al_hs_inv (U : Wp →L[ℂ] Wp) (hU : ∀ v, ‖U v‖ = ‖v‖) (V : Wq →L[ℂ] Wq) (hV : ∀ v, ‖V v‖ = ‖v‖)
    (A B : Wq →L[ℂ] Wp) :
    inner ℂ (hsVec (U.comp (A.comp V))) (hsVec (U.comp (B.comp V))) = inner ℂ (hsVec A) (hsVec B) := by
  let lU : Wp →ₗᵢ[ℂ] Wp := ⟨U.toLinearMap, hU⟩
  let lV : Wq →ₗᵢ[ℂ] Wq := ⟨V.toLinearMap, hV⟩
  let eV : Wq ≃ₗᵢ[ℂ] Wq := lV.toLinearIsometryEquiv rfl
  have h1 : inner ℂ (hsVec (U.comp (A.comp V))) (hsVec (U.comp (B.comp V))) =
      ∑ i, inner ℂ (A (((stdOrthonormalBasis ℂ Wq).map eV) i)) (B (((stdOrthonormalBasis ℂ Wq).map eV) i)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OrthonormalBasis.map_apply]
    exact lU.inner_map_map _ _
  have h2 : inner ℂ (hsVec A) (hsVec B) =
      ∑ i, inner ℂ (A ((stdOrthonormalBasis ℂ Wq) i)) (B ((stdOrthonormalBasis ℂ Wq) i)) := by
    rw [PiLp.inner_apply]
    rfl
  rw [h1, h2, al_sum_inner, al_sum_inner]

theorem al_sgs_tr {p' p : SS k r} (u1 : IsUnit (Matrix.of p'.1.1 : Mat k r).det)
    (u3 : IsUnit (Matrix.of p'.2.1 : Mat k r).det) (g : Mat k r) :
    sgs (tr p' p) g = sgs p (sgs p' g) := by
  show (Matrix.of p'.1.1 * Matrix.of p.1.1)⁻¹ *
      (Matrix.of p'.1.2 * (Matrix.of p'.1.1 * Matrix.of p.1.2 * (Matrix.of p'.1.1)⁻¹))⁻¹ * g *
      (Matrix.of p'.2.2 * (Matrix.of p'.2.1 * Matrix.of p.2.2 * (Matrix.of p'.2.1)⁻¹)) *
      (Matrix.of p'.2.1 * Matrix.of p.2.1) =
    (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ *
      ((Matrix.of p'.1.1)⁻¹ * (Matrix.of p'.1.2)⁻¹ * g * Matrix.of p'.2.2 * Matrix.of p'.2.1) *
      Matrix.of p.2.2 * Matrix.of p.2.1
  simp only [Matrix.mul_assoc, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u1,
    Matrix.nonsing_inv_mul_cancel_left _ _ u1, Matrix.nonsing_inv_mul_cancel_left _ _ u3]

theorem al_rho_tr (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p' p : SS k r} (hp' : D.inSS p')
    (hp : D.inSS p) (g : Mat k r) :
    rho D (tr p' p) F g = (D.π (Matrix.of p'.1.1)).comp
      ((rho D p F (sgs p' g)).comp (D.π' (Matrix.of p'.2.1)⁻¹)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp'
  obtain ⟨g1, g2, g3, g4⟩ := hp
  have e0 := al_sgs_tr (p := p) (WeylGroupFacts.isUnit_of_uh h1.1) (WeylGroupFacts.isUnit_of_uh h3.1) g
  have e1 : D.π (Matrix.of (tr p' p).1.1) = (D.π (Matrix.of p'.1.1)).comp (D.π (Matrix.of p.1.1)) :=
    D.π_rep.2 _ h1 _ g1
  have e2 : D.π' (Matrix.of (tr p' p).2.1)⁻¹ = (D.π' (Matrix.of p.2.1)⁻¹).comp (D.π' (Matrix.of p'.2.1)⁻¹) := by
    have : ((Matrix.of (tr p' p).2.1 : Mat k r))⁻¹ = (Matrix.of p.2.1)⁻¹ * (Matrix.of p'.2.1)⁻¹ :=
      Matrix.mul_inv_rev _ _
    rw [this]
    exact D.π'_rep.2 _ (WeylGroupFacts.uw_inv g3) _ (WeylGroupFacts.uw_inv h3)
  unfold rho
  rw [e0, e1, e2]
  rfl

theorem inner_tr (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p' p : SS k r} (hp' : D.inSS p')
    (hp : D.inSS p) (g : Mat k r) :
    inner ℂ (hsVec (rho D p' F g)) (hsVec (rho D (tr p' p) F g)) =
      hsInner (rho D p F (sgs p' g)) (F (sgs p' g)) := by
  have e : rho D p' F g = (D.π (Matrix.of p'.1.1)).comp ((F (sgs p' g)).comp (D.π' (Matrix.of p'.2.1)⁻¹)) := rfl
  rw [e, al_rho_tr D F hp' hp g]
  exact al_hs_inv _ (D.π_unitary _ hp'.1) _ (D.π'_unitary _ (WeylGroupFacts.uw_inv hp'.2.2.1)) _ _

end alg

section u12

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS properFD

theorem measurable_PhiM (D : RealPlaceData k r Wp Wq) : Measurable (PhiM D) := by
  have e : PhiM D = fun a : ((Fin r → ℂ) × ℂ) × SS k r =>
      mulM (mulM (mulM (mulM (invM a.2.1.1) (invM a.2.1.2)) (gqM D a.1)) a.2.2.2) a.2.2.1 :=
    funext fun a => sgsM_eq a.2 (gqM D a.1)
  rw [e]
  exact meas_mulM (meas_mulM (meas_mulM (meas_mulM (measurable_invM.comp measurable_snd.fst.fst)
    (measurable_invM.comp measurable_snd.fst.snd)) ((measurable_gqM D).comp measurable_fst))
    measurable_snd.snd.snd) measurable_snd.snd.fst

set_option maxHeartbeats 800000 in

theorem sfNu (D : RealPlaceData k r Wp Wq) : SigmaFinite (nuQ D) := by
  unfold nuQ
  first
    | exact SigmaFinite.withDensity_ofReal _
    | exact SigmaFinite.withDensity_ofReal (measurable_bcWeight _ _)
    | infer_instance

theorem u_meas_w (D : RealPlaceData k r Wp Wq) :
    Measurable fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) := by
  exact ENNReal.measurable_ofReal.comp (measurable_bcWeight _ _)

theorem u_meas_inner (D : RealPlaceData k r Wp Wq) {f : Mt k r → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun q : (Fin r → ℂ) × ℂ => ∫⁻ p, f (PhiM D (q, p)) ∂D.μSS := by
  have h1 : Measurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => f (PhiM D a) := hf.comp (measurable_PhiM D)
  exact h1.lintegral_prod_right'

theorem map_Phi (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) :
    ((nuQ D).prod D.μSS).map (PhiM D) = D.μG := by
  have : SigmaFinite (nuQ D) := sfNu D
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h1 : Measurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => f (PhiM D a) := hf.comp (measurable_PhiM D)
  rw [lintegral_map hf (measurable_PhiM D), lintegral_prod _ h1.aemeasurable]
  unfold nuQ
  rw [lintegral_withDensity_eq_lintegral_mul _ (u_meas_w D) (u_meas_inner D hf), hI f hf]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · simp only [Pi.mul_apply, PhiM, gqM_eq D h]
    rfl
  · simp only [Pi.mul_apply, h, ENNReal.ofReal_zero, zero_mul]

theorem sm_KM (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    StronglyMeasurable fun a : SS k r × Mt k r => KM D F a.1 a.2 := by
  have hv : Continuous (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
    (hsL (Wp := Wp) (Wq := Wq)).continuous
  have hc : Continuous fun x : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => inner ℂ (hsVec x.2) (hsVec x.1) :=
    (hv.comp continuous_snd).inner (hv.comp continuous_fst)
  have hp : StronglyMeasurable fun a : SS k r × Mt k r => (RM D F a.1 a.2, FM F a.2) := by
    first
      | exact (sm_RM D hF).prodMk ((sm_FM hF).comp_measurable measurable_snd)
      | exact (sm_RM D hF).prod_mk ((sm_FM hF).comp_measurable measurable_snd)
  exact hc.comp_stronglyMeasurable hp

theorem u_int_test {w : ℝ → ℝ} (h : IsTest w) : Integrable w := by
  exact h.1.continuous.integrable_of_hasCompactSupport h.2.1

theorem u_norm_om_integrand (w : ℝ → ℝ) (x τ : ℝ) :
    ‖(w τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ))‖ = ‖w τ‖ := by
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]

theorem u_continuous_om {w : ℝ → ℝ} (h : IsTest w) : Continuous (om w) := by
  have hw : Continuous w := h.1.continuous
  show Continuous fun x => ∫ τ : ℝ, (w τ : ℂ) * Complex.exp (Complex.I * ((τ * x : ℝ) : ℂ))
  refine continuous_of_dominated (bound := fun τ => ‖w τ‖) (fun x => ?_)
    (fun x => ae_of_all _ fun τ => (u_norm_om_integrand w x τ).le) (u_int_test h).norm (ae_of_all _ fun τ => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    first
      | exact (Complex.continuous_ofReal.comp hw).mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const))))
      | fun_prop
  · first
      | exact continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id))))
      | fun_prop

theorem u_meas_Om (D : RealPlaceData k r Wp Wq) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Measurable (Om D w₁ w₂) := by
  show Measurable fun p : SS k r => om w₁ (lam k r D.z (Matrix.of p.1.2)) * om w₂ (-lam k r D.z' (Matrix.of p.2.2))
  exact ((u_continuous_om h₁).measurable.comp ((continuous_lam D.z).measurable.comp measurable_fst.snd)).mul
    ((u_continuous_om h₂).measurable.comp ((continuous_lam D.z').measurable.comp measurable_snd.snd).neg)

theorem u_aesm_F (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    AEStronglyMeasurable (fun g : Mt k r => F (Matrix.of g)) D.μG := by
  exact jc_aesm_F D hF

theorem u_KM_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    {x : Mt k r} (hx : Matrix.of x ∈ GV k r) :
    KM D F p x = hsInner (rho D p F (Matrix.of x)) (F (Matrix.of x)) := by
  rw [KM, RM_eq D F hp hx, FM_eq F hx]

theorem u_norm_hsInner_le (A B : Wq →L[ℂ] Wp) :
    ‖hsInner A B‖ ≤ ‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2 * (‖A‖ * ‖B‖) := by
  unfold hsInner
  rw [← hsL_apply, ← hsL_apply]
  calc ‖inner ℂ (hsL B) (hsL A)‖ ≤ ‖hsL B‖ * ‖hsL A‖ := norm_inner_le_norm _ _
    _ ≤ (‖hsL (Wp := Wp) (Wq := Wq)‖ * ‖B‖) * (‖hsL (Wp := Wp) (Wq := Wq)‖ * ‖A‖) :=
        mul_le_mul (ContinuousLinearMap.le_opNorm _ B) (ContinuousLinearMap.le_opNorm _ A) (norm_nonneg _) (by positivity)
    _ = ‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2 * (‖A‖ * ‖B‖) := by ring

theorem u_sgs_eq (p : SS k r) (g : Mat k r) :
    sgs p g = (Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * g * (Matrix.of p.2.2 * Matrix.of p.2.1) := by
  first
    | rw [sgs]
    | unfold sgs
  rw [Matrix.mul_inv_rev]
  first
    | (simp only [Matrix.mul_assoc]; done)
    | (simp only [mul_assoc]; done)
    | simp only [Matrix.mul_assoc, mul_assoc]

theorem u_enorm_KM_le (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {p : SS k r} (hp : D.inSS p)
    {x : Mt k r} (hx : Matrix.of x ∈ GV k r) :
    ‖KM D F p x‖ₑ ≤ ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) *
      (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
        ‖F (Matrix.of x)‖ₑ) := by
  rw [u_KM_eq D F hp hx, ← u_sgs_eq, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((u_norm_hsInner_le _ _).trans ?_)
  have := norm_rho_le D hp F (Matrix.of x)
  gcongr

theorem u_lint_KM_le (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ p, D.inSS p → (∫⁻ x, ‖KM D F p x‖ₑ ∂D.μG) ≤
      K * (Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
  obtain ⟨C, hC⟩ := hCB
  obtain ⟨c, hc1, hc2⟩ := hF
  have hcont := contOn_of_CkOn hc1
  have hb : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c := fun g hg =>
    hc2 [] [] (by simp) (by simp) (by simp) g hg
  have hm := u_aesm_F D hcont
  refine ⟨ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * ENNReal.ofReal (C * c * c),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top, fun p hp => ?_⟩
  have hx : Matrix.of p.1.2 * Matrix.of p.1.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.1.1 hp.1.1
  have hy : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have h1 := hC F F c c hm hm hb hb _ hx _ hy
  calc (∫⁻ x, ‖KM D F p x‖ₑ ∂D.μG)
      ≤ ∫⁻ x, ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) *
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F (Matrix.of x)‖ₑ) ∂D.μG := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_mem D.haarG] with x hxG
        exact u_enorm_KM_le D F hp hxG
    _ = ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * ∫⁻ x,
        (‖F ((Matrix.of p.1.2 * Matrix.of p.1.1)⁻¹ * Matrix.of x * (Matrix.of p.2.2 * Matrix.of p.2.1))‖ₑ *
          ‖F (Matrix.of x)‖ₑ) ∂D.μG := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2) * (ENNReal.ofReal (C * c * c) *
          Ξ (Matrix.of p.1.2 * Matrix.of p.1.1) * Ξ (Matrix.of p.2.2 * Matrix.of p.2.1)) := by
        gcongr
    _ = _ := by ring

theorem u_enorm_om_le {w : ℝ → ℝ} (h : IsTest w) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ x : ℝ, ‖om w x‖ₑ ≤ K * ENNReal.ofReal ((1 + |x|) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC⟩ := test_function_decay w h
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun x => ?_⟩
  have hpos : (0 : ℝ) ≤ 1 + |x| := by positivity
  have e : ((1 + |x|) ^ 2)⁻¹ = (1 + |x|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hpos, Real.rpow_two]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul' (by positivity), ← e]
  exact ENNReal.ofReal_le_ofReal (hC x)

def u_fX (z : Fin (2 * r + k + 1) → ℂ) (Ξ : Mat k r → NNReal) (p : Mt k r × Mt k r) : ℝ≥0∞ :=
  Ξ (Matrix.of p.2 * Matrix.of p.1) * ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ)))

theorem u_meas_fX (z : Fin (2 * r + k + 1) → ℂ) {Ξ : Mat k r → NNReal}
    (hΞ : Measurable fun x : Mt k r => Ξ (Matrix.of x)) : Measurable (u_fX z Ξ) := by
  unfold u_fX
  have hm : Measurable fun p : Mt k r × Mt k r => mulM p.2 p.1 := meas_mulM measurable_snd measurable_fst
  have h1 : Measurable fun p : Mt k r × Mt k r => Ξ (Matrix.of (mulM p.2 p.1)) := hΞ.comp hm
  have h1' : Measurable fun p : Mt k r × Mt k r => ((Ξ (Matrix.of p.2 * Matrix.of p.1) : NNReal) : ℝ≥0∞) :=
    h1.coe_nnreal_ennreal
  have hl : Measurable fun p : Mt k r × Mt k r => lam k r z (Matrix.of p.2) :=
    (continuous_lam z).measurable.comp measurable_snd
  have h2 : Measurable fun p : Mt k r × Mt k r => (1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ)) :=
    (measurable_const.add (continuous_abs.measurable.comp hl)).pow_const _
  exact h1'.mul h2.ennreal_ofReal

theorem u_inner_le (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ p, D.inSS p → (∫⁻ x, ‖Om D w₁ w₂ p * KM D F p x‖ₑ ∂D.μG) ≤
      K * (u_fX D.z Ξ p.1 * u_fX D.z' Ξ p.2) := by
  obtain ⟨K0, hK0, h0⟩ := u_lint_KM_le D Ξ A hCB hF
  obtain ⟨K1, hK1, e1⟩ := u_enorm_om_le h₁
  obtain ⟨K2, hK2, e2⟩ := u_enorm_om_le h₂
  refine ⟨K1 * K2 * K0, ENNReal.mul_ne_top (ENNReal.mul_ne_top hK1 hK2) hK0, fun p hp => ?_⟩
  simp only [enorm_mul]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  have a1 := e1 (lam k r D.z (Matrix.of p.1.2))
  have a2 := e2 (-lam k r D.z' (Matrix.of p.2.2))
  rw [abs_neg] at a2
  have a0 := h0 p hp
  have aO : ‖Om D w₁ w₂ p‖ₑ ≤ (K1 * ENNReal.ofReal ((1 + |lam k r D.z (Matrix.of p.1.2)|) ^ (-(2 : ℝ)))) *
      (K2 * ENNReal.ofReal ((1 + |lam k r D.z' (Matrix.of p.2.2)|) ^ (-(2 : ℝ)))) := by
    unfold Om
    rw [enorm_mul]
    exact mul_le_mul' a1 a2
  refine (mul_le_mul' aO a0).trans (le_of_eq ?_)
  unfold u_fX
  ring

theorem u_sm_OmK (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    StronglyMeasurable fun a : SS k r × Mt k r => Om D w₁ w₂ a.1 * KM D F a.1 a.2 := by
  have a1 : StronglyMeasurable fun a : SS k r × Mt k r => Om D w₁ w₂ a.1 :=
    ((u_meas_Om D h₁ h₂).comp measurable_fst).stronglyMeasurable
  have a2 := sm_KM D hF
  exact a1.mul a2

theorem integrable_OmK (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    (hXi : XiInt D Ξ 2) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) :
    Integrable (fun a : SS k r × Mt k r => Om D w₁ w₂ a.1 * KM D F a.1 a.2) (D.μSS.prod D.μG) := by
  have hcont : ContinuousOn F (GV k r) := by
    obtain ⟨c, hc1, _⟩ := hF
    exact contOn_of_CkOn hc1
  have hsm := u_sm_OmK D hcont h₁ h₂
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hsm.enorm.aemeasurable]
  obtain ⟨K, hK, hle⟩ := u_inner_le D Ξ A hCB hF h₁ h₂
  have m1 := (u_meas_fX D.z hXi.1).aemeasurable (μ := D.μW.prod D.μN)
  have m2 := (u_meas_fX D.z' hXi.1).aemeasurable (μ := D.μW'.prod D.μN)
  have f1 : (∫⁻ p, u_fX D.z Ξ p ∂(D.μW.prod D.μN)) < ∞ := hXi.2.1
  have f2 : (∫⁻ p, u_fX D.z' Ξ p ∂(D.μW'.prod D.μN)) < ∞ := hXi.2.2
  calc (∫⁻ p, ∫⁻ x, ‖Om D w₁ w₂ (p, x).1 * KM D F (p, x).1 (p, x).2‖ₑ ∂D.μG ∂D.μSS)
      ≤ ∫⁻ p, K * (u_fX D.z Ξ p.1 * u_fX D.z' Ξ p.2) ∂D.μSS := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_inSS D] with p hp
        exact hle p hp
    _ = K * ((∫⁻ p, u_fX D.z Ξ p ∂(D.μW.prod D.μN)) * ∫⁻ p, u_fX D.z' Ξ p ∂(D.μW'.prod D.μN)) := by
        rw [lintegral_const_mul' _ _ hK]
        unfold RealPlaceData.μSS
        rw [lintegral_prod_mul m1 m2]
    _ < ∞ := ENNReal.mul_lt_top hK.lt_top (ENNReal.mul_lt_top f1 f2)

theorem integrable_GM (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    (hXi : XiInt D Ξ 2) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) : Integrable (GM D F w₁ w₂) D.μG := by
  have h := integrable_OmK D Ξ A hCB hXi hF h₁ h₂
  have h' := h.integral_prod_right
  exact h'

theorem integral_GM (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hCB : CoefBound D Ξ A)
    (hXi : XiInt D Ξ 2) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁)
    (h₂ : IsTest w₂) :
    (∫ x, GM D F w₁ w₂ x ∂D.μG) = ∫ p : SS k r, om w₁ (lam k r D.z (Matrix.of p.1.2)) *
          om w₂ (-lam k r D.z' (Matrix.of p.2.2)) * Ph D F F p ∂D.μSS := by
  have h := integrable_OmK D Ξ A hCB hXi hF h₁ h₂
  have hs := h.swap
  have hswap := integral_integral_swap (μ := D.μG) (ν := D.μSS)
    (f := fun (x : Mt k r) (p : SS k r) => Om D w₁ w₂ p * KM D F p x) hs
  unfold GM
  rw [hswap]
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  rw [integral_const_mul]
  unfold Om Ph
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_mem D.haarG] with x hx
  exact u_KM_eq D F hp hx

end u12

section abstractFubini

theorem v_int_smul {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : P → E} (hu : Integrable u μ) {ξ : P → ℂ} (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1) :
    Integrable (fun p => ξ p • u p) μ := by
  refine hu.mono (hξm.aestronglyMeasurable.smul hu.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [norm_smul, hξ p, one_mul]

theorem v_inner {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ) (ξ : P → ℂ) (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1)
    (hξT : ∀ p p', S p → S p' → ξ (T p p') = ξ p * ξ p')
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (p : P) (hp : S p) :
    inner ℂ (u p) (∫ p', ξ p' • u p' ∂μ) = ξ p * ∫ p', ξ p' * k p p' ∂μ := by
  have hTp := hT p hp
  have e1 : (∫ p', ξ p' • u p' ∂μ) = ∫ p', ξ (T p p') • u (T p p') ∂μ :=
    (hTp.integral_comp (hTe p hp) (fun p' => ξ p' • u p')).symm
  have e2 : (fun p' => ξ (T p p') • u (T p p')) =ᵐ[μ] fun p' => (ξ p * ξ p') • u (T p p') := by
    filter_upwards [hS] with p' hp'
    rw [hξT p p' hp hp']
  have hint : Integrable (fun p' => (ξ p * ξ p') • u (T p p')) μ :=
    v_int_smul ((hTp.integrable_comp_emb (hTe p hp)).2 hu) (measurable_const.mul hξm)
      (fun p' => by rw [norm_mul, hξ, hξ, one_mul])
  rw [e1, integral_congr_ae e2, ← integral_inner hint (u p), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hS] with p' hp'
  rw [inner_smul_right, hk p p' hp hp', mul_assoc]

theorem v_normsq {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ) (ξ : P → ℂ) (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1)
    (hξT : ∀ p p', S p → S p' → ξ (T p p') = ξ p * ξ p')
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p') :
    (((‖∫ p, ξ p • u p ∂μ‖ ^ 2 : ℝ)) : ℂ) = ∫ p, ∫ p', ξ p' * k p p' ∂μ ∂μ := by
  have hi : Integrable (fun p => ξ p • u p) μ := v_int_smul hu hξm hξ
  have h1 : (((‖∫ p, ξ p • u p ∂μ‖ ^ 2 : ℝ)) : ℂ) = inner ℂ (∫ p, ξ p • u p ∂μ) (∫ p, ξ p • u p ∂μ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    try rfl
  rw [h1, ← inner_conj_symm, ← integral_inner hi, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hS] with p hp
  rw [inner_conj_symm, inner_smul_left, v_inner S hS T hT hTe u hu ξ hξm hξ hξT k hk p hp, ← mul_assoc,
    RCLike.conj_mul, hξ p]
  simp

theorem v_kint {P E : Type*} [MeasurableSpace P] {μ : Measure P} [SFinite μ] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (S : P → Prop) (hS : ∀ᵐ p ∂μ, S p) (T : P → P → P)
    (hT : ∀ p, S p → MeasurePreserving (T p) μ μ) (hTe : ∀ p, S p → MeasurableEmbedding (T p))
    (u : P → E) (hu : Integrable u μ)
    (k : P → P → ℂ) (hk : ∀ p p', S p → S p' → inner ℂ (u p) (u (T p p')) = k p p')
    (hkm : AEStronglyMeasurable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ) := by
  have hmp : ∀ p, S p → Integrable (fun p' => ‖u (T p p')‖) μ := fun p hp =>
    (((hT p hp).integrable_comp_emb (hTe p hp)).2 hu).norm
  have hsec : ∀ᵐ p ∂μ, AEStronglyMeasurable (fun p' => k p p') μ := by
    first
      | exact hkm.prodMk_left
      | exact hkm.prod_mk_left
  rw [integrable_prod_iff hkm]
  constructor
  · filter_upwards [hS, hsec] with p hp hpm
    refine Integrable.mono' ((hmp p hp).const_mul ‖u p‖) hpm ?_
    filter_upwards [hS] with p' hp'
    rw [← hk p p' hp hp']
    exact norm_inner_le_norm _ _
  · refine Integrable.mono' (hu.norm.const_mul (∫ x, ‖u x‖ ∂μ)) hkm.norm.integral_prod_right' ?_
    filter_upwards [hS] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc ∫ p', ‖k p p'‖ ∂μ ≤ ∫ p', ‖u p‖ * ‖u (T p p')‖ ∂μ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) ((hmp p hp).const_mul _) ?_
          filter_upwards [hS] with p' hp'
          rw [← hk p p' hp hp']
          exact norm_inner_le_norm _ _
      _ = ‖u p‖ * ∫ x, ‖u x‖ ∂μ := by
          rw [integral_const_mul]
          congr 1
          exact (hT p hp).integral_comp (hTe p hp) (fun x => ‖u x‖)
      _ = (∫ x, ‖u x‖ ∂μ) * ‖u p‖ := mul_comm _ _

theorem v_swap {P T : Type*} [MeasurableSpace P] [MeasurableSpace T] {μ : Measure P} {ν : Measure T}
    [SFinite μ] [SFinite ν]
    (W : T → ℂ) (hW : Integrable W ν) (ξ : T → P → ℂ) (hξm : Measurable (fun a : T × P => ξ a.1 a.2))
    (hξ : ∀ τ p, ‖ξ τ p‖ = 1)
    (k : P → P → ℂ) (hk : Integrable (fun a : P × P => k a.1 a.2) (μ.prod μ)) :
    Integrable (fun τ => W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ) ν ∧
    (∫ τ, W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ ∂ν) =
      ∫ p, ∫ p', (∫ τ, W τ * ξ τ p' ∂ν) * k p p' ∂μ ∂μ := by
  have base : Integrable (fun z : T × (P × P) => W z.1 * k z.2.1 z.2.2) (ν.prod (μ.prod μ)) :=
    hW.mul_prod hk
  have hm : Measurable fun z : T × (P × P) => ξ z.1 z.2.2 :=
    hξm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hInt : Integrable (Function.uncurry fun (τ : T) (a : P × P) => ξ τ a.2 * (W τ * k a.1 a.2))
      (ν.prod (μ.prod μ)) := by
    refine base.mono (hm.aestronglyMeasurable.mul base.1) (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, norm_mul, hξ, one_mul, le_refl]
  have hτ : ∀ τ, W τ * ∫ p, ∫ p', ξ τ p' * k p p' ∂μ ∂μ = ∫ a : P × P, ξ τ a.2 * (W τ * k a.1 a.2) ∂(μ.prod μ) := by
    intro τ
    have hi : Integrable (fun a : P × P => ξ τ a.2 * k a.1 a.2) (μ.prod μ) := by
      have hm' : Measurable fun a : P × P => ξ τ a.2 := hξm.comp (measurable_const.prodMk measurable_snd)
      refine hk.mono (hm'.aestronglyMeasurable.mul hk.1) (ae_of_all _ fun z => ?_)
      simp only [norm_mul, hξ, one_mul, le_refl]
    rw [← integral_prod (fun a : P × P => ξ τ a.2 * k a.1 a.2) hi, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    ring
  constructor
  · have := hInt.integral_prod_left
    refine this.congr (ae_of_all _ fun τ => ?_)
    exact (hτ τ).symm
  · simp_rw [hτ]
    rw [integral_integral_swap hInt]
    have hr := hInt.integral_prod_right
    have e : ∀ a : P × P, (∫ τ, ξ τ a.2 * (W τ * k a.1 a.2) ∂ν) = (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2 := by
      intro a
      rw [← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun τ => ?_)
      ring
    have hr' : Integrable (fun a : P × P => (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2) (μ.prod μ) :=
      hr.congr (ae_of_all _ fun a => e a)
    rw [← integral_prod (fun a : P × P => (∫ τ, W τ * ξ τ a.2 ∂ν) * k a.1 a.2) hr']
    exact integral_congr_ae (ae_of_all _ fun a => e a)

end abstractFubini

section u3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS properFD

theorem w_Phi_eq (D : RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D) (p : SS k r) :
    PhiM D (q, p) = sgs p (gq D q) := by
  show sgsM p (gqM D q) = sgs p (gq D q)
  rw [gqM_eq D hq]
  all_goals rfl

theorem w_hk (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (p p' : SS k r) (hp : D.inSS p) (hp' : D.inSS p') :
    inner ℂ (hsVec (rho D p F (gq D q))) (hsVec (rho D (tr p p') F (gq D q))) = KM D F p' (PhiM D (q, p)) := by
  have hx : Matrix.of (PhiM D (q, p)) ∈ GV k r := by
    rw [w_Phi_eq D hq]
    exact sgs_mem D hp (gq_mem D hq)
  rw [inner_tr D F hp hp' (gq D q), u_KM_eq D F hp' hx, w_Phi_eq D hq]
  all_goals rfl

theorem w_hkm (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r))
    (q : (Fin r → ℂ) × ℂ) :
    StronglyMeasurable (fun a : SS k r × SS k r => KM D F a.2 (PhiM D (q, a.1))) := by
  have hx : Measurable fun a : SS k r × SS k r => PhiM D (q, a.1) := by
    first
      | exact (measurable_PhiM D).comp (measurable_const.prodMk measurable_fst)
      | exact (measurable_PhiM D).comp (measurable_const.prod_mk measurable_fst)
  have h1 : StronglyMeasurable fun a : SS k r × SS k r => RM D F a.2 (PhiM D (q, a.1)) :=
    stronglyMeasurable_rm_comp D hF measurable_snd hx
  have h2 : StronglyMeasurable fun a : SS k r × SS k r => FM F (PhiM D (q, a.1)) := (sm_FM hF).comp_measurable hx
  have hv : Continuous (hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
    (hsL (Wp := Wp) (Wq := Wq)).continuous
  have hc : Continuous fun x : (Wq →L[ℂ] Wp) × (Wq →L[ℂ] Wp) => inner ℂ (hsVec x.2) (hsVec x.1) :=
    (hv.comp continuous_snd).inner (hv.comp continuous_fst)
  first
    | exact hc.comp_stronglyMeasurable (h1.prodMk h2)
    | exact hc.comp_stronglyMeasurable (h1.prod_mk h2)

theorem w_meas_xi (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) : Measurable (xiTau D τ) := by
  first
    | exact (measurable_xi D).comp (measurable_const.prodMk measurable_id)
    | exact (measurable_xi D).comp (measurable_const.prod_mk measurable_id)

theorem w_hJ (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (hint : Integrable (fun p => rho D p F g) D.μSS) (τ : ℝ × ℝ) :
    hsVec (Jtau D τ F g) = ∫ p, xiTau D τ p • hsVec (rho D p F g) ∂D.μSS := by
  have hi : Integrable (fun p => xiTau D τ p • rho D p F g) D.μSS :=
    v_int_smul hint (w_meas_xi D τ) (norm_xi D τ)
  rw [← hsL_apply, Jtau, ← ContinuousLinearMap.integral_comp_comm _ hi]
  simp only [map_smul, hsL_apply]

theorem w_hW {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) volume := by
  have i1 : Integrable w₁ := h₁.1.continuous.integrable_of_hasCompactSupport h₁.2.1
  have i2 : Integrable w₂ := h₂.1.continuous.integrable_of_hasCompactSupport h₂.2.1
  exact (i1.mul_prod i2).ofReal

theorem w_hOm (D : RealPlaceData k r Wp Wq) (w₁ w₂ : ℝ → ℝ) (p : SS k r) :
    (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * xiTau D τ p) = Om D w₁ w₂ p := by
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * xiTau D τ p =
      ((w₁ τ.1 : ℂ) * Complex.exp (Complex.I * ((τ.1 * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ))) *
      ((w₂ τ.2 : ℂ) * Complex.exp (Complex.I * ((τ.2 * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) := by
    intro τ
    rw [xiTau, mul_mul_mul_comm, ← Complex.exp_add]
    have h : Complex.I * (((τ.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ)) : ℂ) =
        Complex.I * ((τ.1 * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ) +
          Complex.I * ((τ.2 * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h]
    simp only [Complex.ofReal_mul]
  simp_rw [e]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul (fun t : ℝ => (w₁ t : ℂ) * Complex.exp (Complex.I * ((t * lam k r D.z (Matrix.of p.1.2) : ℝ) : ℂ)))
    (fun t : ℝ => (w₂ t : ℂ) * Complex.exp (Complex.I * ((t * -lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ)))

theorem w_fixq (D : RealPlaceData k r Wp Wq) (hC : ConjInv D) {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : ContinuousOn F (GV k r)) {q : (Fin r → ℂ) × ℂ} (hq : q ∈ Q0 D)
    (hint : Integrable (fun p => rho D p F (gq D q)) D.μSS) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2) volume ∧
    (((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS := by
  have hu : Integrable (fun p => hsVec (rho D p F (gq D q))) D.μSS := hsL.integrable_comp hint
  have hN : ∀ τ : ℝ × ℝ, (((‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ)) : ℂ) =
      ∫ p, ∫ p', xiTau D τ p' * KM D F p' (PhiM D (q, p)) ∂D.μSS ∂D.μSS := by
    intro τ
    rw [w_hJ D F _ hint τ]
    exact v_normsq D.inSS (ae_inSS D) tr (fun p hp => tr_mp D hC hp) (fun p hp => tr_emb D hp) _ hu
      (xiTau D τ) (w_meas_xi D τ) (norm_xi D τ) (fun p p' hp hp' => xi_tr D τ hp hp')
      (fun p p' => KM D F p' (PhiM D (q, p))) (fun p p' hp hp' => w_hk D F hq p p' hp hp')
  have hki := v_kint D.inSS (ae_inSS D) tr (fun p hp => tr_mp D hC hp) (fun p hp => tr_emb D hp) _ hu
      (fun p p' => KM D F p' (PhiM D (q, p))) (fun p p' hp hp' => w_hk D F hq p p' hp hp')
      (w_hkm D hF q).aestronglyMeasurable
  have sw := v_swap (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ)) (w_hW h₁ h₂) (xiTau D) (measurable_xi D)
    (norm_xi D) (fun p p' => KM D F p' (PhiM D (q, p))) hki
  have e : ∀ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) *
      ∫ p, ∫ p', xiTau D τ p' * KM D F p' (PhiM D (q, p)) ∂D.μSS ∂D.μSS =
      ((w₁ τ.1 * w₂ τ.2 * ‖hsVec (Jtau D τ F (gq D q))‖ ^ 2 : ℝ) : ℂ) := by
    intro τ
    rw [← hN τ, ← Complex.ofReal_mul]
  simp_rw [e, w_hOm] at sw
  refine ⟨?_, ?_⟩
  · refine (sw.1.re).congr (ae_of_all _ fun τ => ?_)
    exact Complex.ofReal_re _
  · exact (integral_complex_ofReal).symm.trans sw.2

end u3

section abstractFinal

theorem lintegral_weighted_swap_ne_top_and_toReal_eq_integral {Tt Q : Type*} [MeasurableSpace Tt] [MeasurableSpace Q] {ν : Measure Tt} {μ : Measure Q}
    [SFinite ν] [SFinite μ]
    (Wt : Tt → ℝ) (hWm : Measurable Wt) (hW0 : ∀ τ, 0 ≤ Wt τ) (w : Q → ℝ) (hwm : Measurable w)
    (hw0 : ∀ q, 0 ≤ w q)
    (n : Tt → Q → ℝ) (hnm : Measurable (fun a : Tt × Q => n a.1 a.2)) (hn0 : ∀ τ q, 0 ≤ n τ q)
    (H : Q → ℂ) (hH : Integrable (fun q => (w q : ℂ) * H q) μ)
    (hgood : ∀ᵐ q ∂μ, w q = 0 ∨
      (Integrable (fun τ => Wt τ * n τ q) ν ∧ ((∫ τ, Wt τ * n τ q ∂ν : ℝ) : ℂ) = H q)) :
    (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) ≠ ∞ ∧
    (((∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν).toReal : ℝ) : ℂ) =
      ∫ q, (w q : ℂ) * H q ∂μ := by
  set B : Q → ℝ := fun q => w q * ∫ τ, Wt τ * n τ q ∂ν with hB
  have hB_eq : ∀ᵐ q ∂μ, ((B q : ℝ) : ℂ) = (w q : ℂ) * H q := by
    filter_upwards [hgood] with q hq
    rcases hq with h | h
    · simp [hB, h]
    · simp only [hB, Complex.ofReal_mul, h.2]
  have hBc : Integrable (fun q => ((B q : ℝ) : ℂ)) μ := hH.congr (hB_eq.mono fun q hq => hq.symm)
  have hBi : Integrable B μ := hBc.re.congr (ae_of_all _ fun q => Complex.ofReal_re _)
  have hB0 : ∀ q, 0 ≤ B q := fun q =>
    mul_nonneg (hw0 q) (integral_nonneg fun τ => mul_nonneg (hW0 τ) (hn0 τ q))
  have hL : (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) =
      ENNReal.ofReal (∫ q, B q ∂μ) := by
    have s1 : (∫⁻ τ, ENNReal.ofReal (Wt τ) * ∫⁻ q, ENNReal.ofReal (w q * n τ q) ∂μ ∂ν) =
        ∫⁻ τ, ∫⁻ q, ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q) ∂μ ∂ν := by
      refine lintegral_congr fun τ => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hm : Measurable (Function.uncurry fun (τ : Tt) (q : Q) =>
        ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q)) := by
      have a1 : Measurable fun a : Tt × Q => ENNReal.ofReal (Wt a.1) := (hWm.comp measurable_fst).ennreal_ofReal
      have a2 : Measurable fun a : Tt × Q => ENNReal.ofReal (w a.2 * n a.1 a.2) :=
        ((hwm.comp measurable_snd).mul hnm).ennreal_ofReal
      exact a1.mul a2
    rw [s1, lintegral_lintegral_swap hm.aemeasurable, ofReal_integral_eq_lintegral_ofReal hBi (ae_of_all _ hB0)]
    refine lintegral_congr_ae ?_
    filter_upwards [hgood] with q hq
    rcases hq with h | h
    · simp [hB, h]
    · have e : ∀ τ, ENNReal.ofReal (Wt τ) * ENNReal.ofReal (w q * n τ q) =
          ENNReal.ofReal (w q * (Wt τ * n τ q)) := by
        intro τ
        rw [← ENNReal.ofReal_mul (hW0 τ)]
        congr 1
        ring
      simp_rw [e]
      rw [← ofReal_integral_eq_lintegral_ofReal (h.1.const_mul _)
        (ae_of_all _ fun τ => mul_nonneg (hw0 q) (mul_nonneg (hW0 τ) (hn0 τ q))), integral_const_mul]
  rw [hL]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (integral_nonneg hB0), ← integral_complex_ofReal]
  exact integral_congr_ae hB_eq

end abstractFinal

section u4

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

attribute [local instance] sfG sfW sfN sfW' sfSS properFD

attribute [local instance] sfNu

theorem boundary_weight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

theorem y_H (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) {G : Mt k r → ℂ} (hG : Integrable G D.μG) :
    Integrable (fun q => ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) *
      ∫ p, G (PhiM D (q, p)) ∂D.μSS) volume ∧
    (∫ q, ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * ∫ p, G (PhiM D (q, p)) ∂D.μSS) =
      ∫ x, G x ∂D.μG := by
  have hmap := map_Phi D hI
  have hPm := measurable_PhiM D
  have hG' : Integrable G (((nuQ D).prod D.μSS).map (PhiM D)) := by rw [hmap]; exact hG
  have hc : Integrable (fun a => G (PhiM D a)) ((nuQ D).prod D.μSS) :=
    (integrable_map_measure hG'.1 hPm.aemeasurable).1 hG'
  have hHν : Integrable (fun q => ∫ p, G (PhiM D (q, p)) ∂D.μSS) (nuQ D) := hc.integral_prod_left
  have hint : (∫ q, ∫ p, G (PhiM D (q, p)) ∂D.μSS ∂(nuQ D)) = ∫ x, G x ∂D.μG := by
    rw [← integral_prod (fun a => G (PhiM D a)) hc, ← hmap, integral_map hPm.aemeasurable hG'.1]
  have hf : Measurable fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) :=
    (measurable_bcWeight _ _).ennreal_ofReal
  have hflt : ∀ᵐ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) < ∞ :=
    ae_of_all _ fun q => ENNReal.ofReal_lt_top
  have e : ∀ q : (Fin r → ℂ) × ℂ, (ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q)).toReal •
      (∫ p, G (PhiM D (q, p)) ∂D.μSS) =
      ((bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℝ) : ℂ) * ∫ p, G (PhiM D (q, p)) ∂D.μSS := by
    intro q
    rw [ENNReal.toReal_ofReal (boundary_weight_nonneg _ _ q), Complex.real_smul]
  constructor
  · have := (integrable_withDensity_iff_integrable_smul' hf hflt).1 hHν
    exact this.congr (ae_of_all _ e)
  · rw [← hint]
    unfold nuQ
    rw [integral_withDensity_eq_integral_toReal_smul hf hflt]
    exact integral_congr_ae (ae_of_all _ fun q => (e q).symm)

theorem y_norm_eq (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) :
    normSqTau D τ F = ∫⁻ q, ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖hsL (JM D F τ q)‖ ^ 2) := by
  unfold normSqTau jNormSq
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · rw [JM_eq D F τ h, hsL_apply]
  · rw [h, zero_mul, zero_mul]

theorem y_meas_n (D : RealPlaceData k r Wp Wq) {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : ContinuousOn F (GV k r)) :
    Measurable fun a : (ℝ × ℝ) × ((Fin r → ℂ) × ℂ) => ‖hsL (JM D F a.1 a.2)‖ ^ 2 := by
  have h0 := sm_JM D hF
  have h1 := (hsL (Wp := Wp) (Wq := Wq)).continuous.comp_stronglyMeasurable h0
  exact (h1.norm.measurable).pow_const 2

theorem y_good (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) (hC : ConjInv D) {A : ℝ} (hCC : CCIntegrable D A)
    {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : InCC A 4 F) {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    ∀ᵐ q : (Fin r → ℂ) × ℂ, bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 ∨
      (Integrable (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2) volume ∧
        ((∫ τ : ℝ × ℝ, w₁ τ.1 * w₂ τ.2 * ‖hsL (JM D F τ q)‖ ^ 2 : ℝ) : ℂ) =
          ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS) := by
  have h1 := (ae_restrict_iff' (measurableSet_Qset D)).1 (jc_ae_integrable D hI hCC hF)
  filter_upwards [h1, ae_mem_good_set_or_weight_zero D] with q hq1 hq2
  rcases hq2 with h | h
  · by_cases hw : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0
    · exact Or.inl hw
    · right
      have hQ : q ∈ Qset D := lt_of_le_of_ne (boundary_weight_nonneg _ _ q) (Ne.symm hw)
      have := w_fixq D hC (jc_cont hF) h (hq1 hQ) h₁ h₂
      simp_rw [JM_eq D F _ h, hsL_apply]
      exact this
  · exact Or.inl h

theorem y_unfold (D : RealPlaceData k r Wp Wq) (Ξ : Mat k r → NNReal) (A : ℝ) (hI : IntFormula D) (hC : ConjInv D)
    (hCC : CCIntegrable D A) (hCB : CoefBound D Ξ A) (hXi : XiInt D Ξ 2) : Unfold D A := by
  intro F hF
  have hc := jc_cont hF
  have hn := y_meas_n D hc
  constructor
  · have hm : Measurable fun a : (ℝ × ℝ) × ((Fin r → ℂ) × ℂ) =>
        ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') a.2 * ‖hsL (JM D F a.1 a.2)‖ ^ 2) :=
      (((measurable_bcWeight _ _).comp measurable_snd).mul hn).ennreal_ofReal
    have h2 := Measurable.lintegral_prod_right' (ν := (volume : Measure ((Fin r → ℂ) × ℂ))) hm
    simp_rw [y_norm_eq D F]
    exact h2.aemeasurable
  · intro w₁ w₂ h₁ h₂ p₁ p₂
    have hG := integrable_GM D Ξ A hCB hXi hF h₁ h₂
    have hH := y_H D hI hG
    have hWm : Measurable fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2 :=
      (h₁.1.continuous.measurable.comp measurable_fst).mul (h₂.1.continuous.measurable.comp measurable_snd)
    have fin := lintegral_weighted_swap_ne_top_and_toReal_eq_integral (ν := (volume : Measure (ℝ × ℝ))) (μ := (volume : Measure ((Fin r → ℂ) × ℂ)))
      (fun τ : ℝ × ℝ => w₁ τ.1 * w₂ τ.2) hWm (fun τ => mul_nonneg (p₁ _) (p₂ _))
      (bcWeight k r (Tz k r D.z) (Tz k r D.z')) (measurable_bcWeight _ _) (boundary_weight_nonneg _ _)
      (fun τ q => ‖hsL (JM D F τ q)‖ ^ 2) hn (fun τ q => by positivity)
      (fun q => ∫ p, GM D F w₁ w₂ (PhiM D (q, p)) ∂D.μSS) hH.1 (y_good D hI hC hCC hF h₁ h₂)
    simp_rw [y_norm_eq D F]
    rw [← integral_GM D Ξ A hCB hXi hF h₁ h₂, ← hH.2]
    exact fin

end u4

theorem y_stepUnfold : Formalism.FourierDecayAlt.B.StepUnfold := by
  intro k r Wp Wq _ _ _ _ _ _ D Ξ A _ hI hC hCC hCB hXi
  exact y_unfold D Ξ A hI hC hCC hCB hXi

end Formalism.FourierDecayAlt.P.B7

namespace Formalism.FourierDecayAlt.P

theorem unfolding_identity_of_integration_formula : Formalism.FourierDecayAlt.B.StepUnfold := B7.y_stepUnfold

theorem orbital_integral_ae_convergence_continuity : Formalism.FourierDecayAlt.B.StepJCont := B7.jc_stepJCont

theorem dilation_identity_of_jacobian : Formalism.FourierDecayAlt.B.StepDilBeta := B7.d_stepDilBeta

end Formalism.FourierDecayAlt.P
