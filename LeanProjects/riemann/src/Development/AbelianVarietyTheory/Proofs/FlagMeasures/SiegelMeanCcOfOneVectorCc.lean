import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanOfWeilSiegel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureGaussian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsOrthComplementOfUnitVectorAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnramifiedAdditiveCharacterConductor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ArchimedeanDensityProductTestFunctionAtSignStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousDensitySelfDualLatticeIndicatorAtUnitStatement

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Count GlobalTheory.GaussMean
open Formalism.MainNotions.S (AutInst uMat)
open scoped TensorProduct Pointwise Topology

noncomputable section

namespace GlobalTheory.OneVectorMean

theorem continuous_qEps {n : ℕ} (ε : Fin n → Bool) : Continuous (qEps ε) := by
  unfold qEps
  fun_prop

theorem qEps_smul {n : ℕ} (ε : Fin n → Bool) (r : ℝ) (y : Fin n → ℂ) : qEps ε (r • y) = r ^ 2 * qEps ε y := by
  simp only [qEps, Finset.mul_sum, Pi.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_isDens {n : ℕ} {ε : Fin n → Bool} {φ : (Fin n → ℂ) → ℝ} {D : ℝ → ℝ} (hc : Continuous φ)
    (hK : HasCompactSupport φ) (h0 : ∀ y, 0 ≤ φ y) (hD : IsDens ε φ D) {β : ℝ} (hβ : β ≠ 0) (hz : D β = 0)
    {y₀ : Fin n → ℂ} (hy : qEps ε y₀ = β) : φ y₀ = 0 := by
  by_contra hne
  have hpos : 0 < φ y₀ := lt_of_le_of_ne (h0 _) (Ne.symm hne)
  set a := φ y₀ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hq := continuous_qEps ε
  have hnb : {p : ℝ × (Fin n → ℂ) | a < φ (p.1 • p.2)} ∈ 𝓝 ((1 : ℝ), y₀) :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simp only [Set.mem_setOf_eq, one_smul]; linarith)
  obtain ⟨V, hV, U', hU', hVU⟩ := mem_nhds_prod_iff.1 hnb
  obtain ⟨ρ, hρ, hU⟩ := Metric.mem_nhds_iff.1 hU'
  set U := Metric.ball y₀ ρ
  haveI : IsFiniteMeasure (volume.restrict U) := ⟨by simpa using measure_ball_lt_top⟩
  let m : Measure ℝ := (volume.restrict U).map (qEps ε)
  let J : Set ℝ := (fun t => √(β / t)) ⁻¹' (V ∩ Set.Icc (1 / 2) 2) ∩ Metric.ball β 1
  have hJ : J ∈ 𝓝 β := by
    have : ContinuousAt (fun t => √(β / t)) β := by fun_prop (disch := exact hβ)
    refine Filter.inter_mem (this.preimage_mem_nhds ?_) (Metric.ball_mem_nhds _ one_pos)
    rw [div_self hβ, Real.sqrt_one]
    exact Filter.inter_mem hV (Icc_mem_nhds (by norm_num) (by norm_num))
  set d := Module.finrank ℝ (Fin n → ℂ)
  have hint : Integrable φ := hc.integrable_of_hasCompactSupport hK
  have hDc : ContinuousAt D β := hD.1.continuousAt (isOpen_ne.mem_nhds hβ)
  have key : ∀ c : NNReal, 0 < c → m J ≤ (c • volume : Measure ℝ) J := fun c hc0 => by
    refine (Besicovitch.vitaliFamily m).measure_le_of_frequently_le _ Measure.AbsolutelyContinuous.rfl J
      fun t ht => (Besicovitch.tendsto_filterAt m t).frequently (Filter.Eventually.frequently ?_)
    set e : ℝ := a * (1 / 2) ^ d * c / 4 with he
    have he0 : 0 < e := by positivity
    have h1 : {s | s ≠ 0 ∧ ‖D s‖ ≤ e} ∈ 𝓝 β :=
      Filter.inter_mem (isOpen_ne.mem_nhds hβ) (hDc.norm.eventually (eventually_le_nhds (by simpa [hz] using he0)))
    obtain ⟨δ₀, hδ₀, h2⟩ := Metric.nhds_basis_closedBall.mem_iff.1 h1
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ₀ / 4 by positivity)] with δ hδ
    obtain ⟨⟨hrV, hr1, hr2⟩, -⟩ := ht
    set r := √(β / t) with hr
    have hbt : 0 < β / t := Real.sqrt_pos.1 (by linarith)
    have ht0 : t ≠ 0 := by rintro rfl; simp at hbt
    have hrr : r ^ 2 * t = β := by rw [hr, Real.sq_sqrt hbt.le]; field_simp
    have hsub : Metric.closedBall β (4 * δ) ⊆ {s | s ≠ 0 ∧ ‖D s‖ ≤ e} :=
      (Metric.closedBall_subset_closedBall (by linarith [hδ.2])).trans h2
    have h3 := hD.2 _ (isCompact_closedBall β (4 * δ)) fun s hs => (hsub hs).1
    have h4 : ∫ s in Metric.closedBall β (4 * δ), D s ≤ e * (2 * (4 * δ)) := by
      refine (Real.le_norm_self _).trans ((norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top
        fun s hs => (hsub hs).2).trans_eq ?_)
      rw [Real.volume_real_closedBall (by linarith [hδ.1])]
    set A := qEps ε ⁻¹' Metric.closedBall t δ ∩ U
    set B := {y | qEps ε y ∈ Metric.closedBall β (4 * δ)}
    have h5 : r • A ⊆ {y | ENNReal.ofReal a ≤ ENNReal.ofReal (φ y)} ∩ B := by
      rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
      refine ⟨ENNReal.ofReal_le_ofReal (hVU (Set.mk_mem_prod hrV (hU hy2))).le, ?_⟩
      change qEps ε (r • y) ∈ Metric.closedBall β (4 * δ)
      rw [qEps_smul, Metric.mem_closedBall, Real.dist_eq, ← hrr, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul (by change r ≤ 2 at hr2; change 1 / 2 ≤ r at hr1; nlinarith) hy1 (abs_nonneg _) (by norm_num)
    have h6 : ENNReal.ofReal (a * (1 / 2) ^ d) * volume A ≤
        ENNReal.ofReal (a * (1 / 2) ^ d) * (c * ENNReal.ofReal (2 * δ)) := by
      calc ENNReal.ofReal (a * (1 / 2) ^ d) * volume A ≤ ENNReal.ofReal a * volume (r • A) := by
            rw [Measure.addHaar_smul, ENNReal.ofReal_mul ha0.le, mul_assoc]
            gcongr
            exact (pow_le_pow_left₀ (by norm_num) hr1 _).trans (le_abs_self _)
        _ ≤ ENNReal.ofReal a * volume.restrict B {y | ENNReal.ofReal a ≤ ENNReal.ofReal (φ y)} := by
            exact mul_le_mul_right ((measure_mono h5).trans (Measure.le_restrict_apply _ _)) _
        _ ≤ ∫⁻ y in B, ENNReal.ofReal (φ y) := mul_meas_ge_le_lintegral hc.measurable.ennreal_ofReal _
        _ = ENNReal.ofReal (∫ y in B, φ y) :=
            (ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Filter.Eventually.of_forall h0)).symm
        _ ≤ ENNReal.ofReal (e * (2 * (4 * δ))) := ENNReal.ofReal_le_ofReal (h3 ▸ h4)
        _ = _ := by
            rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg, ← ENNReal.ofReal_mul (by positivity), he]
            congr 1
            ring
    have h7 : m (Metric.closedBall t δ) = volume A := by
      rw [Measure.map_apply hq.measurable measurableSet_closedBall,
        Measure.restrict_apply (hq.measurable measurableSet_closedBall)]
    change m (Metric.closedBall t δ) ≤ c * volume (Metric.closedBall t δ)
    rw [h7, Real.volume_closedBall]
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top).1 h6
  have hfin : volume J ≠ ⊤ := ((measure_mono Set.inter_subset_right).trans_lt measure_ball_lt_top).ne
  have hlim : Filter.Tendsto (fun c : NNReal => (c : ENNReal) * volume J) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.Tendsto.mul_const (ENNReal.continuous_coe.tendsto (0 : NNReal)) (Or.inr hfin)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hm0 : m J ≤ 0 := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall key)
  have hp : 0 < volume (qEps ε ⁻¹' J ∩ U) := Measure.measure_pos_of_mem_nhds _
    (Filter.inter_mem (hq.continuousAt.preimage_mem_nhds (hy ▸ hJ)) (Metric.ball_mem_nhds _ hρ))
  exact absurd ((Measure.le_restrict_apply _ _).trans ((Measure.le_map_apply hq.aemeasurable J).trans hm0)) hp.not_ge

theorem lintegral_lt_top_of_meanC {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (G : α → ENNReal)
    (hG : Measurable G) (hfin : ∀ a, G a ≠ ⊤) (h : meanC μ S (fun a => ((G a).toReal : ℂ)) ≠ 0) :
    ∫⁻ a in S, G a ∂μ < ⊤ := by
  have h1 : Integrable (fun a => ((G a).toReal : ℂ)) (μ.restrict S) := by
    by_contra h1
    exact h (by unfold meanC; rw [integral_undef h1, smul_zero])
  exact ((integrable_toReal_iff hG.aemeasurable (Filter.Eventually.of_forall hfin)).1 (by simpa using h1.re)).lt_top

variable (I : AutInst) (φ : InfinitePlace I.F → (Fin I.n → ℂ) → ℝ)

open Classical in

def term (x : I.GA) (y : Fin I.n → I.E) : ℝ :=
  if y ∈ lamX I x then ∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) else 0

theorem term_nonneg (h0 : ∀ v y, 0 ≤ φ v y) (x : I.GA) (y : Fin I.n → I.E) : 0 ≤ term I φ x y := by
  unfold term
  split_ifs
  · exact Finset.prod_nonneg fun v _ => h0 _ _
  · exact le_rfl

theorem measurable_term (hc : ∀ v, Continuous (φ v)) (y : Fin I.n → I.E) :
    Measurable fun x : I.GA => ENNReal.ofReal (term I φ x y) := by
  classical
  obtain ⟨h1, -⟩ := GlobalTheory.StabUnfold.gaussAt_meas_inv I y
  have h2 : ∀ v, Measurable fun g : Formalism.REAL.UJ (I.ε v) =>
      φ v (((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) := fun v => by
    have hc' : Continuous fun g : Formalism.REAL.UJ (I.ε v) => (uMat g)⁻¹ := by
      simp only [GlobalTheory.StabUnfold.uMat_inv_eq]
      exact Units.continuous_coe_inv.comp continuous_subtype_val
    exact ((hc v).comp ((hc'.matrix_mul continuous_const).matrix_mulVec continuous_const)).measurable
  unfold term
  exact (Measurable.ite (measurable_snd h1.measurableSet)
    (Finset.measurable_prod _ fun v _ => (h2 v).comp ((measurable_pi_apply v).comp measurable_fst))
    measurable_const).ennreal_ofReal

theorem finite_term (hK : ∀ v, HasCompactSupport (φ v)) (x : I.GA) : {y | term I φ x y ≠ 0}.Finite := by
  have hb : ∀ v, ∃ C : ℝ, ∀ z ∈ tsupport (φ v), ‖(I.P v * uMat (x.1 v)) *ᵥ z‖ ≤ C := fun v =>
    (hK v).isCompact.exists_bound_of_continuousOn (continuous_const.matrix_mulVec continuous_id).continuousOn
  choose C hC using hb
  obtain ⟨B, hB⟩ := (Set.finite_range C).bddAbove
  refine (GlobalTheory.RatDiscrete.finite_bounded (lamX I x)
    (Module.Finite.iff_fg.2 (GlobalTheory.PointLattice.lamX_selfDual I x).2.1) B).subset fun y hy => ?_
  have hy : term I φ x y ≠ 0 := hy
  unfold term at hy
  have hx : y ∈ lamX I x := by
    by_contra hx
    exact hy (if_neg hx)
  rw [if_pos hx] at hy
  refine ⟨hx, fun τ i => ?_⟩
  obtain ⟨v, hv⟩ := GlobalTheory.RatDiscrete.exists_place I τ
  have h1 := hC v _ (subset_tsupport _ (Finset.prod_ne_zero_iff.1 hy v (Finset.mem_univ v)))
  have h2 : IsUnit (I.P v * uMat (x.1 v)).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 ((I.P_unit v).mul (Units.isUnit _))
  rw [← Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h2, Matrix.one_mulVec] at h1
  rw [hv]
  exact (norm_le_pi_norm (fun i => I.φ v (y i)) i).trans (h1.trans (hB ⟨v, rfl⟩))

theorem qEps_frame (s : Bool) (y : Fin I.n → I.E) (hy : star y ⬝ᵥ (I.J *ᵥ y) = sgn I.E s) (v : InfinitePlace I.F)
    (g : Formalism.REAL.UJ (I.ε v)) : qEps (I.ε v) (((uMat g)⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)) = sgn ℝ s := by
  have hφ : ∀ a : I.E, I.φ v (star a) = star (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  have hs : star (fun i => I.φ v (y i)) = fun i => I.φ v (star y i) := by
    funext i; simp [hφ]
  have hg : (uMat g⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * uMat g⁻¹ = Formalism.REAL.Jm (I.ε v) := g⁻¹.2
  have hF : ((uMat g)⁻¹ * (I.P v)⁻¹)ᴴ * Formalism.REAL.Jm (I.ε v) * ((uMat g)⁻¹ * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← GlobalTheory.StabUnfold.frame_inv_form I v, GlobalTheory.StabUnfold.uMat_inv_eq, Matrix.conjTranspose_mul]
    conv_rhs => rw [← hg]
    simp only [Matrix.mul_assoc]
  apply Complex.ofReal_injective
  rw [GlobalTheory.StabUnfold.ofReal_qEps_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hF, hs]
  have e : ((sgn ℝ s : ℝ) : ℂ) = I.φ v (sgn I.E s) := by
    unfold sgn; split_ifs <;> simp
  rw [e, ← hy]
  simp [dotProduct, mulVec, map_sum]

theorem hE_eq (y : Fin I.n → I.E) : hE I.cm.sig I.J y y = star y ⬝ᵥ (I.J *ᵥ y) := by
  simp only [hE, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rfl

theorem sum_eq (β : I.E) (x : I.GA) :
    (∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
      ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))) =
      ∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β}, ENNReal.ofReal (term I φ x (X.1 0)) := by
  rw [tsum_subtype {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β}
    fun X => ENNReal.ofReal (term I φ x (X 0)), ← (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm.tsum_eq]
  refine (tsum_subtype {y : Fin I.n → I.E | y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β} fun y =>
    ENNReal.ofReal (∏ v, φ v (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y i)))).trans
    (tsum_congr fun y => ?_)
  by_cases h : star y ⬝ᵥ (I.J *ᵥ y) = β
  · rw [Set.indicator_of_mem (a := (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm y)
      (by exact (hE_eq I y).trans h)]
    change _ = ENNReal.ofReal (term I φ x y)
    unfold term
    by_cases hy : y ∈ lamX I x
    · rw [Set.indicator_of_mem (by exact ⟨hy, h⟩), if_pos hy]
    · rw [Set.indicator_of_notMem (fun h' => hy h'.1), if_neg hy, ENNReal.ofReal_zero]
  · have h1 : (Equiv.funUnique (Fin 1) (Fin I.n → I.E)).symm y ∉
        {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = β} := fun h' => by
      have h'' : hE I.cm.sig I.J y y = β := h'
      exact h ((hE_eq I y).symm.trans h'')
    rw [Set.indicator_of_notMem (fun h' => h h'.2), Set.indicator_of_notMem h1]

theorem sum_ne_top (hK : ∀ v, HasCompactSupport (φ v)) (A : Set (Fin 1 → Fin I.n → I.E)) (x : I.GA) :
    ∑' X : A, ENNReal.ofReal (term I φ x (X.1 0)) ≠ ⊤ := by
  have h := (finite_term I φ hK x).preimage (f := fun X : A => X.1 0)
    fun X _ Y _ hXY => Subtype.ext (funext fun i => by rw [Subsingleton.elim i 0]; exact hXY)
  rw [tsum_eq_sum (s := h.toFinset) fun X hX => by
    have : term I φ x (X.1 0) = 0 := by simpa using hX
    rw [this, ENNReal.ofReal_zero]]
  exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top

theorem test_eq_term (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v)) (T : HA (AF I.F) I.cm.sig I.J ≃ₜ* I.GA)
    (hf : ∀ h, I.fmat (T h).2 = (Formalism.MainNotions.StandardLattice.finMat I.cm.sig I.J h).map (Algebra.TensorProduct.comm I.F _ _))
    (hi : ∀ v h, uMat ((T h).1 v) = (I.P v)⁻¹ * Formalism.MainNotions.StandardLattice.infMat I.cm.sig I.J (θ v) h * I.P v)
    (h : HA (AF I.F) I.cm.sig I.J) (X : Fin 1 → Fin I.n → I.E) :
    ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (projInf (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i)) : ℝ) : ℂ) *
      {Y : Fin 1 → Fin I.n → Af I.F ⊗[I.F] I.E | Y 0 ∈ Formalism.MainNotions.StandardLattice.latHat I.F I.E (I.L : Set (Fin I.n → I.E))}.indicator
        (1 : (Fin 1 → Fin I.n → Af I.F ⊗[I.F] I.E) → ℂ) (projFin (h⁻¹ • ratTup (F := I.F) (AF I.F) X)) =
      (term I φ (T h) (X 0) : ℂ) := by
  have e0 : ∀ i, (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i =
      ∑ j, (HA.mat (AF I.F) I.cm.sig I.J h⁻¹).1 i j * ((1 : AF I.F) ⊗ₜ[I.F] X 0 j) := fun i => rfl
  have e1 : projFin (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 ∈ Formalism.MainNotions.StandardLattice.latHat I.F I.E (I.L : Set (Fin I.n → I.E)) ↔
      X 0 ∈ lamX I (T h) := by
    rw [GlobalTheory.T.mem_adelicLatticeClosure_iff_swap_mem_span, (GlobalTheory.PointLattice.lamX_selfDual I (T h)).1, show (T h).2⁻¹ = (T h⁻¹).2 by rw [map_inv]; rfl, hf]
    refine iff_of_eq (congrArg (· ∈ I.Lf) (funext fun i => ?_))
    simp only [projFin, e0, map_sum, map_mul, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have e2 : ∀ v, ((I.P v)⁻¹ *ᵥ fun i => θ v (projInf (h⁻¹ • ratTup (F := I.F) (AF I.F) X) 0 i)) =
      ((uMat ((T h).1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (X 0 i) := fun v => by
    rw [GlobalTheory.StabUnfold.uMat_inv_eq, show ((T h).1 v)⁻¹ = (T h⁻¹).1 v by rw [map_inv]; rfl, hi,
      Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)),
      ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp only [projInf, e0, map_sum, map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, (hθ v).1]
    rfl
  unfold term
  by_cases hx : X 0 ∈ lamX I (T h)
  · rw [if_pos hx, Set.indicator_of_mem (by exact e1.2 hx), Pi.one_apply, mul_one]
    simp only [e2]
  · rw [if_neg hx, Set.indicator_of_notMem (by exact fun h' => hx (e1.1 h')), mul_zero, Complex.ofReal_zero]

theorem test_smooth (θ : InfinitePlace I.F → (Ainf I.F ⊗[I.F] I.E →+* ℂ))
    (hθ : ∀ v, Formalism.MainNotions.StandardLattice.IsInfEmb (I.φ v) (θ v))
    (hs : ∀ v, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ v)) (hK : ∀ v, HasCompactSupport (φ v))
    (Φ : (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) → ℂ)
    (hΦ : Φ = fun X => ((∏ v, φ v ((I.P v)⁻¹ *ᵥ fun i => θ v (X 0 i)) : ℝ) : ℂ)) :
    Continuous Φ ∧ HasCompactSupport Φ ∧
      ∀ (N : ℕ) (e : (Fin 1 → Fin I.n → Ainf I.F ⊗[I.F] I.E) ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ ∘ e.symm) := by
  obtain ⟨T, hT⟩ := GlobalTheory.GaussMean.RealDensity.exists_coord_space I θ hθ
  let Ψ : (InfinitePlace I.F → Fin I.n → ℂ) → ℂ := fun z => ((∏ v, φ v (z v) : ℝ) : ℂ)
  have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ :=
    Complex.ofRealCLM.contDiff.comp (contDiff_prod fun v _ => (hs v).comp (contDiff_apply ℝ _ v))
  have hΨK : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro (isCompact_univ_pi fun v => (hK v).isCompact) fun z hz => ?_
    obtain ⟨v, hv⟩ : ∃ v, z v ∉ tsupport (φ v) := by simpa using hz
    simp only [Ψ]
    rw [Finset.prod_eq_zero (f := fun v => φ v (z v)) (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport (f := φ v) hv),
      Complex.ofReal_zero]
  have e0 : Φ = Ψ ∘ T := by
    funext X
    simp only [hΦ, Ψ, Function.comp_apply, hT]
  rw [e0]
  refine ⟨hΨ.continuous.comp T.continuous, hΨK.comp_homeomorph T.toHomeomorph, fun N e _ he => ?_⟩
  exact hΨ.comp ((e.symm.trans T.toAddEquiv).toAddMonoidHom.toRealLinearMap (T.continuous.comp he)).contDiff

theorem siegelMeanCc_of_oneVectorCc : OneVectorCc → SiegelMeanCc := by
  intro hW I hn s μf _ _ fund hfund
  obtain ⟨hCM, hJ, T, hT1, hT2, hT3⟩ := GlobalTheory.T.exists_adelic_unitaryGroup_models_equiv I
  obtain ⟨a1, b1⟩ := hW I.F I.E I.cm.sig hCM I.n I.J hJ
  choose θ hθ using fun v => (GlobalTheory.Mem.VolEmb.existsUnique_infEmb _ _ _ hCM (I.φ v)).exists
  obtain ⟨μ, S, hμ, hS, hTm, hvol, hint⟩ := GlobalTheory.SiegelWeilMean.exists_transport I T hT1 μf fund hfund
  have hfin : μ S < ⊤ := (a1.2 μ hμ).2 S hS
  refine ⟨hvol ▸ hfin, fun φ D hφ => ?_⟩
  have hc : ∀ v, Continuous (φ v) := fun v => (hφ v).1.continuous
  have hK : ∀ v, HasCompactSupport (φ v) := fun v => (hφ v).2.1
  have h0 : ∀ v y, 0 ≤ φ v y := fun v => (hφ v).2.2.1
  have hs1 : ∀ (R : Type) [Ring R] [Nontrivial R], sgn R s ≠ 0 := fun R _ _ => by cases s <;> simp [sgn]
  by_cases hD : ∏ v, D v (sgn ℝ s) = 0
  · obtain ⟨v, -, hv⟩ := Finset.prod_eq_zero_iff.1 hD
    rw [hD, mul_zero, ENNReal.ofReal_zero, mul_zero]
    refine (lintegral_congr fun x => ENNReal.tsum_eq_zero.2 fun y => ?_).trans lintegral_zero
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (eq_zero_of_isDens (hc v) (hK v) (h0 v) (hφ v).2.2.2 (hs1 ℝ) hv
      (qEps_frame I s y.1 y.2.2 v _)), ENNReal.ofReal_zero]
  have hL : Submodule.IsLattice I.E I.L := ⟨I.L_fg, I.L_span⟩
  haveI : FiniteDimensional I.F I.E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  let b := Module.finBasis I.F I.E
  obtain ⟨g1, g2, g3⟩ := test_smooth I φ θ hθ (fun v => (hφ v).1) hK _ rfl
  have hΦ := test_eq_term I φ θ hθ T hT2 fun v => hT3 v (θ v) (hθ v)
  have hsg : ∀ (R : Type) [CommRing R] [Algebra I.F R], algebraMap I.F R (sgn I.F s) = sgn R s := fun R _ _ => by
    cases s <;> simp [sgn]
  obtain ⟨⟨ψ, hψ⟩, hB⟩ := b1 hn (sgn I.F s) (hs1 _) _ b _ _ _ _ g1 g2 g3
    ⟨GlobalTheory.T.isSchwartzBruhat_indicator_localLatticeCompletion I.F I.E I.n I.L hL, (GlobalTheory.T.eventually_localLatticeCompletion_eq_coordinateLattice I.F I.E I.n _ b I.L hL).mono fun v hv => by rw [hv],
      GlobalTheory.T.indicator_completedLattice_eq_finprod_local I.F I.E I.n I.L hL⟩ fun _ => rfl
  obtain ⟨⟨μi, hμi⟩, ⟨νi, hνi⟩, ⟨μv, hμv⟩, ⟨νv, hνv⟩, hQ⟩ := ((hB ψ hψ).2 μ hμ).2 S hS
  obtain ⟨Fi, Fl, hFi, hFl, -, hmean⟩ := hQ μi νi μv νv hμi hνi hμv hνv
  obtain ⟨lam, m, hlam, hψi, hm, hdual, hprod⟩ := GlobalTheory.T.adelic_character_frequencies_and_conductor_product I θ hθ ψ hψ
  obtain ⟨hE1, hE2, hE3⟩ := GlobalTheory.T.cm_euler_product_discr_unramified I I.n (by omega)
  obtain ⟨n1, n2, n3, -, n5, -⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hreal := GlobalTheory.T.archimedean_density_product_testFunction_at_sign I θ hθ lam _ hlam hψi μi νi hμi hνi φ D (fun v => ⟨hc v, hK v, (hφ v).2.2.2⟩) Fi hFi s
  have hloc : ∀ u, Fl u (algebraMap I.F (Fv I.F u) (sgn I.F s)) =
      (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ m u) ^ ((1 / 2 : ℝ) - (I.n : ℝ)) *
        (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta I.F I.E u ^ I.n * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard I.F u ^ I.n)⁻¹) : ℝ) : ℂ) := fun u => by
    obtain ⟨Lv, h1, h2⟩ := GlobalTheory.T.exists_selfDualLattice_completion_maxOrder I.F I.E I.cm.sig I.n I.J I.L hJ hL I.L_dual u
    refine GlobalTheory.T.continuousDensity_selfDualLatticeIndicator_at_unit I.F I.E I.cm.sig hCM I.n (by omega) I.J hJ u (hE3 u) (GlobalTheory.LocalDensityValue.localChar I.F ψ u)
      (GlobalTheory.LocalDensityValue.isLocalChar I.F ψ hψ u (m u) (hdual u)) (m u) (hdual u) Lv h1
      _ _ (hμv u) (hνv u) _ (by simpa only [h2] using hFl u) _ ?_
    rw [hsg]
    cases s <;> simp [sgn]
  have hw : 0 < Formalism.HermitianLatticesTheory.vInv I.E := by linarith
  rw [hsg I.E, hsg (Ainf I.F), hreal, tprod_congr hloc, GlobalTheory.SiegelWeilMean.const_eq _
    (fun u => zero_lt_one.trans (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.one_lt_resCard I.F u))
    m hm _ _ hE1 lam _ hlam (Formalism.HermitianLatticesTheory.vInv I.E) hw I.n I.f n5 (by rw [← hE2]; exact hprod)] at hmean
  rw [← hint, ← hvol]
  haveI : Countable I.E := (Module.finBasis ℚ I.E).equivFun.toEquiv.countable_iff.2 inferInstance
  simp only [sum_eq I φ]
  have hG : Measurable fun h : HA (AF I.F) I.cm.sig I.J =>
      ∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = sgn I.E s},
        ENNReal.ofReal (term I φ (T h) (X.1 0)) :=
    Measurable.ennreal_tsum fun X => (measurable_term I φ hc _).comp hTm
  have hM : meanC μ S (fun h => ((∑' X : {X : Fin 1 → Fin I.n → I.E | hE I.cm.sig I.J (X 0) (X 0) = sgn I.E s},
      ENNReal.ofReal (term I φ (T h) (X.1 0))).toReal : ℂ)) =
      ((meanConst I.E I.n * ∏ v, D v (sgn ℝ s) : ℝ) : ℂ) := by
    unfold meanConst
    rw [n1, ← hmean]
    congr 1
    funext h
    rw [ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top, Complex.ofReal_tsum]
    exact tsum_congr fun X => by rw [ENNReal.toReal_ofReal (term_nonneg _ _ h0 _ _), ← hΦ]
  have hL0 := (GlobalTheory.DensityEuler.hasProd_eulerFac I.cm.cmUnram I.n (by omega)).2
  have hc0 : 0 < meanConst I.E I.n := by unfold meanConst; positivity
  exact GlobalTheory.SiegelWeilMean.lintegral_eq_of_meanC μ S hfin _ hG
    (lintegral_lt_top_of_meanC μ S _ hG (fun h => sum_ne_top I φ hK _ _)
      (hM ▸ Complex.ofReal_ne_zero.2 (mul_ne_zero hc0.ne' hD))) _ hM

end GlobalTheory.OneVectorMean
