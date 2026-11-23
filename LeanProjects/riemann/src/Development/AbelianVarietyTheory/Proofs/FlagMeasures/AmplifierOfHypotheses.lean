import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellDataSupport
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HaarEqSmul
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumNormSqEqTrace

open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpOrb

theorem sfinite_of_lintegral {X : Type} [MeasurableSpace X] (ν : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F ν)
    (h0 : ∀ᵐ x ∂ν, F x ≠ 0) (h1 : ∫⁻ x, F x ∂ν ≠ ⊤) : SFinite ν := by
  haveI := isFiniteMeasure_withDensity h1
  rw [← withDensity_inv_same₀ hF h0 ((ae_lt_top' hF h1).mono fun x hx => hx.ne)]
  infer_instance

theorem mp_of_weil {X A : Type} [MeasurableSpace X] [MeasurableSpace A] (P ν : Measure X) (μ : Measure A) [SFinite μ]
    (act : A → X → X) (hm : Measurable fun q : X × A => act q.2 q.1)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (act a x) ∂μ) ∂ν) :
    MeasurePreserving (fun q : X × A => act q.2 q.1) (ν.prod μ) P := by
  refine ⟨hm, ?_⟩
  ext s hs
  have h1 : Measurable (s.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hs
  rw [← lintegral_indicator_one hs, ← lintegral_indicator_one hs, lintegral_map h1 hm, hW _ h1,
    lintegral_prod (fun q : X × A => s.indicator (1 : X → ℝ≥0∞) (act q.2 q.1)) (h1.comp hm).aemeasurable]

theorem sfinite_of_weil {X A : Type} [MeasurableSpace X] [MeasurableSpace A] (P ν : Measure X) (μ : Measure A)
    [SFinite μ] [SigmaFinite P] (hμ : μ ≠ 0)
    (act : A → X → X) (hm : Measurable fun q : X × A => act q.2 q.1)
    (hW : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (act a x) ∂μ) ∂ν) : SFinite ν := by
  obtain ⟨g, g0, gm, g1⟩ := exists_pos_lintegral_lt_of_sigmaFinite P (ε := 1) one_ne_zero
  have gm' : Measurable fun x => (g x : ℝ≥0∞) := gm.coe_nnreal_ennreal
  refine sfinite_of_lintegral ν (fun x => ∫⁻ a, g (act a x) ∂μ)
    (Measurable.lintegral_prod_right' (gm'.comp hm)).aemeasurable (Filter.Eventually.of_forall fun x => ?_) ?_
  · intro h
    have hx : Measurable fun a => (g (act a x) : ℝ≥0∞) := (gm'.comp hm).comp measurable_prodMk_left
    rw [lintegral_eq_zero_iff hx] at h
    apply hμ
    rw [← ae_eq_bot, ← Filter.eventually_false_iff_eq_bot]
    filter_upwards [h] with a ha
    exact (g0 _).ne' (by simpa using ha)
  · rw [← hW _ gm']; exact (g1.trans ENNReal.one_lt_top).ne

theorem double_weil {X Y A E : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P ν : Measure X) (Q ρ : Measure Y) (μ : Measure A)
    [SFinite P] [SFinite ν] [SFinite Q] [SFinite ρ] [SFinite μ] (a₁ : A → X → X) (a₂ : A → Y → Y)
    (h₁ : MeasurePreserving (fun q : X × A => a₁ q.2 q.1) (ν.prod μ) P)
    (h₂ : MeasurePreserving (fun q : Y × A => a₂ q.2 q.1) (ρ.prod μ) Q)
    (K : X × Y → E) (hK : AEStronglyMeasurable K (P.prod ρ)) (hI : Integrable K (ν.prod Q))
    (hinv : ∀ᵐ t ∂((ν.prod μ).prod ρ), K (a₁ t.1.2 t.1.1, t.2) = K (t.1.1, a₂ t.1.2 t.2)) :
    ∫ y, ∫ x, K (x, y) ∂P ∂ρ = ∫ x, ∫ y, K (x, y) ∂Q ∂ν := by
  have f1 : MeasurePreserving (fun t : (X × A) × Y => (a₁ t.1.2 t.1.1, t.2)) ((ν.prod μ).prod ρ) (P.prod ρ) :=
    h₁.prod (MeasurePreserving.id ρ)
  have f2 : MeasurePreserving (fun t : (X × A) × Y => (t.1.1, a₂ t.1.2 t.2)) ((ν.prod μ).prod ρ) (ν.prod Q) :=
    ((MeasurePreserving.id ν).prod (h₂.comp Measure.measurePreserving_swap)).comp (measurePreserving_prodAssoc ν μ ρ)
  have i2 := f2.integrable_comp_of_integrable hI
  have i1 : Integrable K (P.prod ρ) := (f1.integrable_comp hK).1 (i2.congr (hinv.mono fun t ht => ht.symm))
  rw [← integral_prod_symm _ i1, ← integral_prod _ hI]
  have e1 := integral_map f1.aemeasurable (f := K) (by rw [f1.map_eq]; exact hK)
  have e2 := integral_map f2.aemeasurable (f := K) (by rw [f2.map_eq]; exact hI.1)
  rw [f1.map_eq] at e1
  rw [f2.map_eq] at e2
  rw [e1, e2]
  exact integral_congr_ae hinv

theorem integral_comm_of_norm {X E F : Type} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (μ : Measure X) (T : E →L[ℝ] F)
    (c : ℝ) (hT : ∀ e, ‖T e‖ = c * ‖e‖) (f : X → E) : ∫ x, T (f x) ∂μ = T (∫ x, f x ∂μ) := by
  by_cases hf : Integrable f μ
  · exact T.integral_comp_comm hf
  rw [integral_undef hf, map_zero]
  by_cases hc : c ≤ 0
  · have : ∀ e, T e = 0 := fun e => norm_le_zero_iff.1 (by rw [hT]; exact mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg _))
    simp [this]
  push_neg at hc
  have ha : AntilipschitzWith (c⁻¹).toNNReal T := AddMonoidHomClass.antilipschitz_of_bound T fun e => by
    rw [hT, Real.coe_toNNReal _ (by positivity), ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  exact integral_undef fun h => hf ((T.lipschitz.integrable_comp_iff_of_antilipschitz ha (map_zero T)).1 h)

section RankOne
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def rkB : E →L[ℝ] F →L[ℝ] (F →L[ℂ] E) :=
  LinearMap.mkContinuous₂ (LinearMap.mk₂ ℝ (fun (a : E) (b : F) => (innerSL ℂ b).smulRight a)
    (fun a a' b => by ext w; simp)
    (fun t a b => by ext w; simp [smul_comm t])
    (fun a b b' => by ext w; simp [add_smul])
    (fun t a b => by
      ext w
      simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.smul_apply]
      rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, mul_smul, Complex.coe_smul])) 1
    (fun a b => by simp [mul_comm])

theorem rkB_apply (a : E) (b : F) : rkB a b = (innerSL ℂ b).smulRight a := rfl

theorem norm_rkB (a : E) (b : F) : ‖rkB a b‖ = ‖a‖ * ‖b‖ := by simp [rkB_apply, mul_comm]

theorem integral_prod_rankOne [CompleteSpace E] [CompleteSpace F] {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (a : X → E) (b : Y → F) :
    ∫ z : X × Y, (innerSL ℂ (b z.2)).smulRight (a z.1) ∂(μ.prod ν) =
      (innerSL ℂ (∫ y, b y ∂ν)).smulRight (∫ x, a x ∂μ) := by
  simp only [← rkB_apply]
  by_cases h : Integrable (fun z : X × Y => rkB (a z.1) (b z.2)) (μ.prod ν)
  · rw [integral_prod _ h]
    have e1 : ∀ x, ∫ y, rkB (a x) (b y) ∂ν = rkB (a x) (∫ y, b y ∂ν) := fun x =>
      integral_comm_of_norm ν (rkB (a x)) ‖a x‖ (fun e => norm_rkB _ _) b
    have e2 := integral_comm_of_norm μ ((rkB (E := E) (F := F)).flip (∫ y, b y ∂ν)) ‖∫ y, b y ∂ν‖
      (fun e => by rw [ContinuousLinearMap.flip_apply, norm_rkB, mul_comm]) a
    simp only [ContinuousLinearMap.flip_apply] at e2
    simp only [e1]
    exact e2
  have H : ¬Integrable a μ ∨ ¬Integrable b ν := by
    contrapose! h
    exact h.1.op_fst_snd (op := fun a b => rkB a b) (rkB (E := E) (F := F)).continuous₂
      ⟨1, fun a b => by rw [norm_rkB, one_mul]⟩ h.2
  rcases H with H | H <;> simp [integral_undef h, integral_undef H]

theorem integral_apply_of_norm [CompleteSpace E] {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → (E →L[ℂ] E))
    (hT : AEStronglyMeasurable T μ) (ξ : E) (h : ∀ᵐ x ∂μ, ‖T x‖ * ‖ξ‖ ≤ ‖T x ξ‖) :
    (∫ x, T x ∂μ) ξ = ∫ x, T x ξ ∂μ := by
  by_cases hf : Integrable T μ
  · exact ContinuousLinearMap.integral_apply hf ξ
  by_cases hξ : ξ = 0
  · simp [hξ]
  rw [integral_undef hf, integral_undef, ContinuousLinearMap.zero_apply]
  intro hi
  refine hf ((hi.norm.div_const ‖ξ‖).mono' hT ?_)
  filter_upwards [h] with x hx
  rwa [le_div_iff₀ (norm_pos_iff.2 hξ)]

end RankOne

variable {k r : ℕ}

theorem meas_mul {α : Type} [MeasurableSpace α] {f g : α → Mt k r} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => (Matrix.of.symm (Matrix.of (f x) * Matrix.of (g x)) : Mt k r)) :=
  Formalism.FourierDecayAlt.P.B7.continuous_mulM.measurable.comp (hf.prodMk hg)

theorem meas_inv {α : Type} [MeasurableSpace α] {f : α → Mt k r} (hf : Measurable f) :
    Measurable (fun x => (Matrix.of.symm (Matrix.of (f x))⁻¹ : Mt k r)) :=
  Formalism.FourierDecayAlt.P.B7.measurable_invM.comp hf

theorem mp_inv_haarLie (S : Set (MatKR k r)) (κ : ℝ≥0∞) :
    MeasurePreserving (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) (haarLie S κ) (haarLie S κ) := by
  have hm : Measurable (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  refine ⟨hm, ?_⟩
  unfold haarLie
  rw [Measure.map_smul]
  congr 1
  set e : lieE S → Mt k r := fun x i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with he
  by_cases h : AEMeasurable e volume
  · rw [AEMeasurable.map_map_of_aemeasurable hm.aemeasurable h]
    have : Formalism.FourierDecayAlt.B2.invM ∘ e = e ∘ Neg.neg := by
      funext x
      show (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)))⁻¹ =
        NormedSpace.exp (unrealify (-x.1))
      rw [← Matrix.exp_neg]
      exact congrArg NormedSpace.exp (by ext i j; simp [unrealify, Complex.ext_iff])
    rw [this, ← AEMeasurable.map_map_of_aemeasurable (by rwa [Measure.map_neg_eq_self]) measurable_neg.aemeasurable,
      Measure.map_neg_eq_self]
  · simp [Measure.map_of_not_aemeasurable h]

def side {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : MatKR k r → (W →L[ℂ] W)) (σ : MatKR k r → (H →L[ℂ] H)) (u v : H)
    (ξ : W) (s : Mt k r × Mt k r) : W :=
  (psi k r z c (Matrix.of s.2) * ⟪v, σ ((Matrix.of s.1)⁻¹ * (Matrix.of s.2)⁻¹) u⟫_ℂ) • π (Matrix.of s.1) ξ

theorem integral_side {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {π : MatKR k r → (W →L[ℂ] W)} {σ : MatKR k r → (H →L[ℂ] H)} (u v : H)
    (ξ : W) (hz : inWb k r z) (hT : 0 < Tz k r z) (hk : 1 ≤ k) {t : Fin k → ℝ} (hπ : PI.UpqRep.IsHCTypeW k r z t π)
    {μW : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z) μW) (κ : ℝ≥0∞)
    (hσ : ContinuousOn (fun g => σ g u) (UH (Hpk k r))) :
    ∫ s, side z c π σ u v ξ s ∂(μW.prod (haarLie (Nset k r) κ)) =
      Formalism.FourierDecayAlt.ThreeDimData.be z c π σ μW (haarLie (Nset k r) κ) u v ξ := by
  set μN := haarLie (Nset k r) κ with hμN
  have : SFinite μN := by rw [hμN]; unfold haarLie; infer_instance
  have : SigmaFinite μW := hW.1
  have hWB := ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μW).2.2 z hz hT hk).1 hW
  have hm : Measurable (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  have iW : MeasurePreserving (Formalism.FourierDecayAlt.B2.invM (k := k) (r := r)) μW μW :=
    ⟨hm, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μW (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) hWB⟩
  have hTm := iW.prod (mp_inv_haarLie (Nset k r) κ)
  have hπc : ContinuousOn π (UWset k r z) := continuousOn_clm_apply.mpr (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_cont hT hπ)
  have hπu := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary hT hπ
  let U : Set (Mt k r × Mt k r) :=
    {p | (Matrix.of p.1 : MatKR k r) ∈ UWset k r z ∧ (Matrix.of p.2 : MatKR k r) ∈ Nset k r}
  have aW : ∀ᵐ y ∂μW, Matrix.of y ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have hUae : ∀ᵐ p ∂(μW.prod μN), p ∈ U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae aW,
      Measure.quasiMeasurePreserving_snd.ae (GlobalTheory.CellOrbInt.ae_mem_N (k := k) (r := r) κ)] with p a b
    exact ⟨a, b⟩
  have c1 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.1 : MatKR k r)) := continuous_fst
  have c2 : Continuous (fun p : Mt k r × Mt k r => (Matrix.of p.2 : MatKR k r)) := continuous_snd
  have hUm : MeasurableSet U :=
    (((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k r z).preimage c1).inter
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k r).preimage c2)).measurableSet
  have hcont : ContinuousOn (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ u v) U := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
    have k1 : ContinuousOn (fun p : Mt k r × Mt k r => σ (Matrix.of p.1 * Matrix.of p.2) u) U :=
      hσ.comp (c1.matrix_mul c2).continuousOn fun p hp => Formalism.FourierDecayAlt.P.DDSmoothness.uh_mul hp.1.1 hp.2.1
    have k2 : Continuous (fun p : Mt k r × Mt k r => star (psi k r z c (Matrix.of p.2))) :=
      ((GlobalTheory.CellOrbInt.continuous_psi z c).comp continuous_snd).star
    have k3 : ContinuousOn (fun p : Mt k r × Mt k r => (Matrix.of p.1 : MatKR k r)⁻¹) U :=
      (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp c1.continuousOn fun p hp => hp.1.1
    have k4 : ContinuousOn (fun p : Mt k r × Mt k r => π (Matrix.of p.1 : MatKR k r)⁻¹) U :=
      hπc.comp k3 fun p hp => (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1).1
    exact ((continuousOn_const.inner (𝕜 := ℂ) k1).mul k2.continuousOn).smul k4
  have hb : AEStronglyMeasurable (Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ u v) (μW.prod μN) := by
    have := hcont.aestronglyMeasurable (μ := μW.prod μN) hUm
    rwa [Measure.restrict_eq_self_of_ae_mem hUae] at this
  unfold Formalism.FourierDecayAlt.ThreeDimData.be
  rw [integral_apply_of_norm _ _ hb ξ]
  · have e1 := integral_map hTm.aemeasurable (f := fun p => Formalism.FourierDecayAlt.ThreeDimData.beInt z c π σ u v p ξ)
      (by rw [hTm.map_eq]; exact hb.apply_continuousLinearMap ξ)
    rw [hTm.map_eq] at e1
    rw [e1]
    refine integral_congr_ae ?_
    filter_upwards [hUae] with p hp
    have h3 := ((GlobalTheory.BesselPsi.psi_character k r z c hz).2.2.1 _ hp.2).2
    have h4 : ((Matrix.of p.1 : MatKR k r)⁻¹)⁻¹ = Matrix.of p.1 :=
      Matrix.nonsing_inv_nonsing_inv _ ((Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ hp.1.1)
    show _ = ((⟪v, σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) u⟫_ℂ * star (psi k r z c (Matrix.of p.2)⁻¹)) •
      π ((Matrix.of p.1 : MatKR k r)⁻¹)⁻¹) ξ
    rw [h3, h4, star_star, mul_comm]
    rfl
  · filter_upwards [hUae] with p hp
    have hi := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.1).1
    have hπ1 : ‖π (Matrix.of p.1 : MatKR k r)⁻¹‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [hπu _ hi, one_mul]
    unfold Formalism.FourierDecayAlt.ThreeDimData.beInt
    rw [ContinuousLinearMap.smul_apply, norm_smul, norm_smul, hπu _ hi]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) hπ1) (norm_nonneg _)

def lA (γ : MatKR k r) (p : PairSp k r) : MatKR k r := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ

def lB (p : PairSp k r) : MatKR k r := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹

def opM (L : LocBessel k r) (γ : MatKR k r) (ξ : L.Wp) (ξ' : L.Wq) (p : PairSp k r) : L.Wq →L[ℂ] L.Wp :=
  besselIntg L (fun _ => (innerSL ℂ ξ').smulRight ξ) γ p

def ker (L : LocBessel k r) (γ : MatKR k r) (w v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) (q : PairSp k r × Mt k r) :
    L.Wq →L[ℂ] L.Wp :=
  (⟪v, L.σ (lA γ q.1 * Matrix.of q.2) w⟫_ℂ * star ⟪v', L.σ (lB q.1 * Matrix.of q.2) w⟫_ℂ) • opM L γ ξ ξ' q.1

open GlobalTheory.CellOrbInt

theorem lA_mem (L : LocBessel k r) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) {p : PairSp k r} (hp : p ∈ pairSet L) :
    lA γ p ∈ UH (Hpk k r) :=
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hp.1.1) _ (hG.inv_mem _ hp.2.1.1)) _ hγ

theorem lB_mem (L : LocBessel k r) {p : PairSp k r} (hp : p ∈ pairSet L) : lB p ∈ UH (Hpk k r) :=
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  hG.mul_mem _ (hG.inv_mem _ hp.2.2.1.1) _ (hG.inv_mem _ hp.2.2.2.1)

theorem lA_lB (L : LocBessel k r) (γ : MatKR k r) {p : PairSp k r} (hp : p ∈ pairSet L) :
    lA γ p * (lB p)⁻¹ =
      (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  unfold lA lB
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ hp.2.2.1.1),
    Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ hp.2.2.2.1), ← Matrix.mul_assoc]

theorem aesm_ker (L : LocBessel k r) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) (w v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (μ : Measure (PairSp k r)) (ρ : Measure (Mt k r)) [SFinite ρ] (hμ : ∀ᵐ p ∂μ, p ∈ pairSet L)
    (hρ : ∀ᵐ x ∂ρ, Matrix.of x ∈ UH (Hpk k r)) : AEStronglyMeasurable (ker L γ w v v' ξ ξ') (μ.prod ρ) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  let U : Set (PairSp k r × Mt k r) := pairSet L ×ˢ {x | Matrix.of x ∈ UH (Hpk k r)}
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have hUm : MeasurableSet U := (meas_pairSet L).prod hcl.measurableSet
  have hUae : ∀ᵐ q ∂(μ.prod ρ), q ∈ U := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμ, Measure.quasiMeasurePreserving_snd.ae hρ] with p a b
    exact ⟨a, b⟩
  have inv : ∀ f : PairSp k r × Mt k r → MatKR k r, Continuous f → (∀ q ∈ U, f q ∈ UH (Hpk k r)) →
      ContinuousOn (fun q => (f q)⁻¹) U := fun f hf h =>
    (Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp hf.continuousOn h
  have cx : ContinuousOn (fun q : PairSp k r × Mt k r => (Matrix.of q.2 : MatKR k r)) U := continuous_snd.continuousOn
  have cA : ContinuousOn (fun q : PairSp k r × Mt k r => lA γ q.1 * Matrix.of q.2) U :=
    (((inv (fun q => Matrix.of q.1.1.1) continuous_fst.fst.fst fun q hq => hq.1.1.1).mul
      (inv (fun q => Matrix.of q.1.1.2) continuous_fst.fst.snd fun q hq => hq.1.2.1.1)).mul continuousOn_const).mul cx
  have cB : ContinuousOn (fun q : PairSp k r × Mt k r => lB q.1 * Matrix.of q.2) U :=
    ((inv (fun q => Matrix.of q.1.2.1) continuous_fst.snd.fst fun q hq => hq.1.2.2.1.1).mul
      (inv (fun q => Matrix.of q.1.2.2) continuous_fst.snd.snd fun q hq => hq.1.2.2.2.1)).mul cx
  have s1 := (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w).comp cA fun q hq => hG.mul_mem _ (lA_mem L hγ hq.1) _ hq.2
  have s2 := (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w).comp cB fun q hq => hG.mul_mem _ (lB_mem L hq.1) _ hq.2
  have cM : ContinuousOn (fun q : PairSp k r × Mt k r => opM L γ ξ ξ' q.1) U :=
    (contOn_intg L hγ continuousOn_const).comp continuous_fst.continuousOn fun q hq => hq.1
  have hc : ContinuousOn (ker L γ w v v' ξ ξ') U :=
    ((continuousOn_const.inner (𝕜 := ℂ) s1).mul (continuousOn_const.inner (𝕜 := ℂ) s2).star).smul cM
  haveI : BorelSpace (PairSp k r) := Prod.borelSpace
  haveI : BorelSpace (PairSp k r × Mt k r) := Prod.borelSpace
  have := hc.aestronglyMeasurable (μ := μ.prod ρ) hUm
  rwa [Measure.restrict_eq_self_of_ae_mem hUae] at this

theorem ker_act (L : LocBessel k r) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    (w v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) {a : MatKR k r} (ha : a ∈ RStab k r γ) {p : PairSp k r}
    (hp : p ∈ pairSet L) (x : Mt k r) :
    ker L γ w v v' ξ ξ' (stabAct γ a p, x) =
      ker L γ w v v' ξ ξ' (p, Matrix.of.symm (γ⁻¹ * a⁻¹ * γ * Matrix.of x)) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have uγ := hG.unit _ hγ
  have e1 : lA γ (stabAct γ a p) * Matrix.of x = lA γ p * (γ⁻¹ * a⁻¹ * γ * Matrix.of x) := by
    show (Matrix.of p.1.1)⁻¹ * (a * Matrix.of p.1.2)⁻¹ * γ * Matrix.of x = _
    simp only [lA, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ uγ]
  have e2 : lB (stabAct γ a p) * Matrix.of x = lB p * (γ⁻¹ * a⁻¹ * γ * Matrix.of x) := by
    show (Matrix.of p.2.1)⁻¹ * (γ⁻¹ * a * γ * Matrix.of p.2.2)⁻¹ * Matrix.of x = _
    simp only [lB, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.nonsing_inv_nonsing_inv _ uγ]
  have e3 : opM L γ ξ ξ' (stabAct γ a p) = opM L γ ξ ξ' p := by
    obtain ⟨n1, m1, -⟩ := GlobalTheory.BesselPsi.psi_character k r L.z L.c L.hz.1
    obtain ⟨n2, m2, -⟩ := GlobalTheory.BesselPsi.psi_character k r L.z' L.c L.hz'.1
    show (psi k r L.z L.c (a * Matrix.of p.1.2) * star (psi k r L.z' L.c (γ⁻¹ * a * γ * Matrix.of p.2.2))) • _ = _
    rw [(m1 _ ha.1 _ hp.2.1).2, (m2 _ ha.2 _ hp.2.2.2).2, ← hrel a ha, star_mul']
    have : psi k r L.z L.c a * star (psi k r L.z L.c a) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, n1]; simp
    rw [mul_mul_mul_comm, this, one_mul]
    rfl
  unfold ker
  rw [e1, e2, e3]
  rfl

theorem integral_ker_pair (L : LocBessel k r) (hk : 1 ≤ k) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r))
    (hmul : ∀ g ∈ UH (Hpk k r), ∀ h ∈ UH (Hpk k r), ∀ v, L.σ (g * h) v = L.σ g (L.σ h v))
    (w v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) {x : Mt k r} (hx : Matrix.of x ∈ UH (Hpk k r)) :
    ∫ p, ker L γ w v v' ξ ξ' (p, x) ∂(pairMeas L) =
      (innerSL ℂ (Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ (Matrix.of x) w) v' ξ')).smulRight
        (Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ (γ * Matrix.of x) w) v ξ) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have : SFinite (haarLie (Nset k r) L.κN) := by unfold haarLie; infer_instance
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have e1 := integral_side L.c (σ := L.σ) (L.σ (γ * Matrix.of x) w) v ξ L.hz.1 L.hz.2 hk (t := L.u) L.hπ L.hμW.1 L.κN
    (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ _)
  have e2 := integral_side L.c (σ := L.σ) (L.σ (Matrix.of x) w) v' ξ' L.hz'.1 L.hz'.2 hk (t := L.u') L.hπ' L.hμW'.1
    L.κN (Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ _)
  unfold LocBessel.μN
  rw [← e1, ← e2, ← integral_prod_rankOne]
  refine integral_congr_ae ?_
  filter_upwards [ae_pairMeas L] with p hp
  have h1 := hG.mul_mem _ (hG.inv_mem _ hp.1.1) _ (hG.inv_mem _ hp.2.1.1)
  ext η
  have h2 := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_inner L.hz'.2 (u := L.u') L.hπ' (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uw_inv hp.2.2.1).1 ξ' η
  rw [Matrix.nonsing_inv_nonsing_inv _ (hG.unit _ hp.2.2.1.1)] at h2
  simp only [ker, opM, besselIntg, side, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, smul_smul, inner_smul_left, h2]
  rw [← hmul _ h1 _ (hG.mul_mem _ hγ _ hx),
    ← hmul _ (hG.mul_mem _ (hG.inv_mem _ hp.2.2.1.1) _ (hG.inv_mem _ hp.2.2.2.1)) _ hx, ← Matrix.mul_assoc]
  congr 1
  simp only [lA, lB, map_mul, Complex.star_def]
  ring

theorem integral_ker_group (L : LocBessel k r) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r))
    (hmul : ∀ g ∈ UH (Hpk k r), ∀ h ∈ UH (Hpk k r), ∀ v, L.σ (g * h) v = L.σ g (L.σ h v))
    (hone : ∀ v, L.σ 1 v = v)
    (huni : ∀ g ∈ UH (Hpk k r), ∀ v w, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {μG : Measure (Mt k r)} (hμ : ∀ᵐ x ∂μG, Matrix.of x ∈ UH (Hpk k r)) {w : L.Hs} {d : ℂ}
    (hS : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG = d * ⟪y, y'⟫_ℂ)
    (v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq) {p : PairSp k r} (hp : p ∈ pairSet L) :
    ∫ x, ker L γ w v v' ξ ξ' (p, x) ∂μG = d • besselIntg L (coefF L v v' ξ ξ') γ p := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have adj : ∀ g ∈ UH (Hpk k r), ∀ y ∈ UH (Hpk k r), ∀ a b : L.Hs,
      ⟪a, L.σ (g * y) b⟫_ℂ = ⟪L.σ g⁻¹ a, L.σ y b⟫_ℂ := by
    intro g hg y hy a b
    rw [← huni g hg (L.σ g⁻¹ a), ← hmul _ hg _ (hG.inv_mem _ hg), Matrix.mul_nonsing_inv _ (hG.unit _ hg), hone,
      hmul _ hg _ hy]
  have hA := lA_mem L hγ hp
  have hB := lB_mem L hp
  have e : ∫ x, ⟪v, L.σ (lA γ p * Matrix.of x) w⟫_ℂ * star ⟪v', L.σ (lB p * Matrix.of x) w⟫_ℂ ∂μG =
      d * ⟪v, L.σ (lA γ p * (lB p)⁻¹) v'⟫_ℂ := by
    rw [adj _ hA _ (hG.inv_mem _ hB), ← hS]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [adj _ hA _ hx, adj _ hB _ hx]
  unfold ker
  simp only
  rw [integral_smul_const, e, lA_lB L γ hp, mul_smul]
  congr 1
  ext η
  simp only [opM, besselIntg, coefF_eq, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul]
  rw [smul_comm]

theorem rpow_bound {s t u b e : ℝ} (hs : 1 ≤ s) (ht : 1 ≤ t) (hu : 1 ≤ u) (h : u ≤ s * t) (hb : 0 ≤ b) (he : b ≤ e) :
    s ^ (-e) * t ^ (-e) ≤ u ^ (-b) * t ^ (-(e - b)) := by
  have h1 : s ^ (-e) ≤ s ^ (-b) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  have h2 : (s * t) ^ (-b) ≤ u ^ (-b) := Real.rpow_le_rpow_of_nonpos (by linarith) h (by linarith)
  have h3 : t ^ (-e) = t ^ (-b) * t ^ (-(e - b)) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [Real.mul_rpow (by linarith) (by linarith)] at h2
  rw [h3, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right h1 (by positivity)).trans h2) (by positivity)

theorem integrable_ker (L : LocBessel k r) {γ : MatKR k r} (hγ : γ ∈ UH (Hpk k r)) (w v v' : L.Hs) (ξ : L.Wp)
    (ξ' : L.Wq) {μG : Measure (Mt k r)} (hμ : IsHaarOn (UH (Hpk k r)) μG) {ν : Measure (PairSp k r)} [SFinite ν]
    (hν : ∀ᵐ p ∂ν, p ∈ pairSet L) {b e C C' : ℝ} (hb : 0 ≤ b) (he : Formalism.FourierDecayAlt.ThreeDimData.AG k r < e - b)
    (hint : Integrable (pairMaj γ b) ν)
    (hC : ∀ x ∈ UH (Hpk k r), ‖⟪v, L.σ x w⟫_ℂ‖ ≤ C * Formalism.FourierDecayAlt.B.gN x ^ (-e))
    (hC' : ∀ x ∈ UH (Hpk k r), ‖⟪v', L.σ x w⟫_ℂ‖ ≤ C' * Formalism.FourierDecayAlt.B.gN x ^ (-e)) :
    Integrable (ker L γ w v v' ξ ξ') (ν.prod μG) := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  haveI : SigmaFinite μG := hμ.1
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have hAG : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have i1 := hint.mul_prod (GlobalTheory.gN_rpow_neg_integrable_haar k r μG (e - b) hμ he)
  have sk : MeasurePreserving (fun q : PairSp k r × Mt k r => (id q.1, lmulM (lB q.1) q.2)) (ν.prod μG) (ν.prod μG) :=
    (MeasurePreserving.id ν).skew_product (g := fun p x => lmulM (lB p) x)
      (meas_mul (meas_mul (meas_inv measurable_fst.snd.fst) (meas_inv measurable_fst.snd.snd)) measurable_snd)
      (hν.mono fun p hp => hμ.2.2.2 _ (lB_mem L hp))
  have i2 := (sk.integrable_comp_of_integrable i1).const_mul (|C| * |C'| * ‖(innerSL ℂ ξ').smulRight ξ‖)
  refine i2.mono' (aesm_ker L hγ w v v' ξ ξ' ν μG hν aG) ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν, Measure.quasiMeasurePreserving_snd.ae aG] with q hp hx
  have hA := hG.mul_mem _ (lA_mem L hγ hp) _ hx
  have hB := hG.mul_mem _ (lB_mem L hp) _ hx
  have hu := point_mem L hγ hp
  have e1 : (Matrix.of q.1.1.1)⁻¹ * (Matrix.of q.1.1.2)⁻¹ * γ * Matrix.of q.1.2.2 * Matrix.of q.1.2.1 =
      (lA γ q.1 * Matrix.of q.2) * (lB q.1 * Matrix.of q.2)⁻¹ := by
    rw [← lA_lB L γ hp, Matrix.mul_inv_rev, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hG.unit _ hx)]
  have key := rpow_bound (PI.PolynomialProperness.GN.gN_ge_one hA) (PI.PolynomialProperness.GN.gN_ge_one hB) (PI.PolynomialProperness.GN.gN_ge_one hu)
    (b := b) (e := e) (by
      rw [e1]
      exact (GlobalTheory.ThA.FrobNorm.gN_mul_le _ _).trans (le_of_eq (by rw [GlobalTheory.ThA.FrobNorm.gN_inv hB]))) hb (by linarith)
  have p1 : 0 ≤ Formalism.FourierDecayAlt.B.gN (lA γ q.1 * Matrix.of q.2) ^ (-e) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have p2 : 0 ≤ Formalism.FourierDecayAlt.B.gN (lB q.1 * Matrix.of q.2) ^ (-e) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have b1 := (hC _ hA).trans (mul_le_mul_of_nonneg_right (le_abs_self C) p1)
  have b2 := (hC' _ hB).trans (mul_le_mul_of_nonneg_right (le_abs_self C') p2)
  have b3 : ‖opM L γ ξ ξ' q.1‖ ≤ ‖(innerSL ℂ ξ').smulRight ξ‖ := norm_intg_le L γ _ hp
  unfold ker
  rw [norm_smul, norm_mul, norm_star]
  have q1 := mul_nonneg (abs_nonneg C) p1
  have q2 := mul_nonneg (abs_nonneg C') p2
  refine (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) q1) b3 (norm_nonneg _) (mul_nonneg q1 q2)).trans ?_
  rw [mul_mul_mul_comm, mul_right_comm]
  exact mul_le_mul_of_nonneg_left key (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _))

theorem ampKF : BranchingSupport.Hyps → GlobalTheory.CellAmp.AmpKF := by
  intro H _ k r L h μG w l l' hOne γ μR νR ν hD b hb0 hb hint v v' hv hv' ξ ξ'
  obtain ⟨⟨hgap, hok, -, hw, hμ, -, -⟩, hl, hl'⟩ := hOne
  obtain ⟨hγ, -, -, hrel, hR, hQ, hQG⟩ := hD
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  let R : Rep k r := ⟨L.Hs, L.σ⟩
  have hDS : R.IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  obtain ⟨hmul, hone, huni, -⟩ := GlobalTheory.rep_basic_of_isDS H.1.2.2.1 k r L.ε L.lam R hDS
  have hsm := H.1.2.2.1 k r L.ε L.lam L.Hs L.σ L.hlam hσ w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw)
  obtain ⟨C, Ws, -, hC⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v hv
  obtain ⟨C', Ws', -, hC'⟩ := H.1.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hok v' hv'
  have hw1 : ‖w‖ = 1 := hw.choose_spec.2.1
  have hw0 : w ≠ 0 := fun h0 => by simp [h0] at hw1
  obtain ⟨c, -, hc⟩ := GlobalTheory.BesselDegree.schur_fdeg H k r L.ε μG hμ
  obtain ⟨hd, hS⟩ := hc L.lam R hDS
  have hd' : PI.BesselPeriodGGP.fdegH μG L.σ w = c * fdegHC L.lam := hd w hw0
  have hS' : ∀ y y' : L.Hs, ∫ x, ⟪y, L.σ (Matrix.of x) w⟫_ℂ * star ⟪y', L.σ (Matrix.of x) w⟫_ℂ ∂μG =
      (PI.BesselPeriodGGP.fdegH μG L.σ w : ℂ)⁻¹ * ⟪y, y'⟫_ℂ := fun y y' => by
    refine (hS w y w y').2.trans ?_
    have : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
    rw [hd']
    show ⟪w, w⟫_ℂ * ⟪y, y'⟫_ℂ / _ = _
    rw [this, one_mul, div_eq_inv_mul]
  haveI : SigmaFinite μG := hμ.1
  haveI : SigmaFinite μR := hR.1
  haveI : SFinite (pairMeas L) := by
    have : SFinite L.μN := by unfold LocBessel.μN haarLie; infer_instance
    have : SigmaFinite L.μW := L.hμW.1.1
    have : SigmaFinite L.μW' := L.hμW'.1.1
    unfold pairMeas; infer_instance
  have aG : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by rw [ae_iff]; exact hμ.2.2.1
  have aR : ∀ᵐ y ∂μR, Matrix.of y ∈ RStab k r γ := by rw [ae_iff]; exact hR.2.2.1
  have aν := ae_quot L hR hQ
  haveI : SFinite ν := sfinite_of_lintegral ν (fun p => ‖pairMaj γ b p‖ₑ) hint.1.enorm
    (aν.mono fun p hp => by
      have : 0 < pairMaj γ b p :=
        Real.rpow_pos_of_pos (one_pos.trans_le (PI.PolynomialProperness.GN.gN_ge_one (point_mem L hγ hp))) _
      simpa using this.ne') hint.2.ne
  have hRc := Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (hG.unit _ hγ)
  have hinv : μR.map GlobalTheory.SgInf.invM = μR :=
    (GlobalTheory.UnipUnimod.isUnimod_of_subset_Nset (S := RStab k r γ)
      ⟨fun a ha => ha.1.1, hRc.closed, hRc.one_mem, hRc.mul_mem, hRc.inv_mem⟩ (fun a ha => ha.1) hR).2
  have mi : Measurable (GlobalTheory.SgInf.invM (k := k) (r := r)) := Formalism.FourierDecayAlt.P.B7.measurable_invM
  let cj : Mt k r → Mt k r := fun x => fun i j => (γ⁻¹ * Matrix.of x * γ) i j
  have mc : Measurable cj :=
    meas_mul (g := fun _ => γ) (meas_mul (f := fun _ => (γ⁻¹ : MatKR k r)) measurable_const measurable_id)
      measurable_const
  let a₂ : Mt k r → Mt k r → Mt k r := fun a x => Matrix.of.symm (γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x)
  have m2 : Measurable fun q : Mt k r × Mt k r => a₂ q.2 q.1 :=
    meas_mul (mc.comp (mi.comp measurable_snd)) measurable_fst
  have hW2 : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, (∫⁻ a, f (a₂ a x) ∂μR) ∂νR := by
    intro f hf
    rw [hQG f hf]
    refine lintegral_congr fun x => ?_
    have mf : Measurable fun s : Mt k r => f fun i j => (Matrix.of s * Matrix.of x) i j :=
      hf.comp (meas_mul measurable_id measurable_const)
    rw [lintegral_map mf mc]
    conv_lhs => rw [← hinv]
    rw [lintegral_map (f := fun s => f fun i j => (Matrix.of (cj s) * Matrix.of x) i j) (mf.comp mc) mi]
    rfl
  haveI : SFinite νR := sfinite_of_weil μG νR μR hR.2.1 a₂ m2 hW2
  have m1 : Measurable fun q : PairSp k r × Mt k r => stabAct γ (Matrix.of q.2) q.1 :=
    (measurable_fst.fst.fst.prodMk (meas_mul measurable_snd measurable_fst.fst.snd)).prodMk
      (measurable_fst.snd.fst.prodMk (meas_mul (mc.comp measurable_snd) measurable_fst.snd.snd))
  have hcl : IsClosed {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := hG.closed
  have aνR : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk k r) := by
    refine ae_of_weil μG νR μR a₂ _ hcl.measurableSet aG hR.2.1 hW2 ?_
    filter_upwards [aR] with a ha x hx
    have h1 := hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ hγ) _ (hG.inv_mem _ ha.1.1)) _ hγ
    have h3 : γ⁻¹ * (Matrix.of a)⁻¹ * γ * Matrix.of x ∈ UH (Hpk k r) := hx
    have h2 := hG.mul_mem _ (hG.inv_mem _ h1) _ h3
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (hG.unit _ h1)] at h2
    exact h2
  have hI := integrable_ker L hγ w v v' ξ ξ' hμ aν (e := Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) hb0 (by linarith) hint
    (fun x hx => by rw [neg_sub]; exact hC w hsm x hx) (fun x hx => by rw [neg_sub]; exact hC' w hsm x hx)
  have key := double_weil (pairMeas L) ν μG νR μR (fun a p => stabAct γ (Matrix.of a) p) a₂
    (mp_of_weil _ _ _ (fun a p => stabAct γ (Matrix.of a) p) m1 hQ) (mp_of_weil _ _ _ a₂ m2 hW2)
    (ker L γ w v v' ξ ξ') (aesm_ker L hγ w v v' ξ ξ' _ _ (ae_pairMeas L) aνR) hI (by
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae aν).and
        (Measure.quasiMeasurePreserving_snd.ae aR))] with t ht
      exact ker_act L hγ hrel w v v' ξ ξ' ht.2 ht.1 t.2)
  unfold ampJ OrbInt
  rw [Complex.ofReal_one, inv_one, one_smul, ← integral_smul, ← integral_smul]
  refine Eq.trans (integral_congr_ae ?_) (key.trans (integral_congr_ae ?_))
  · filter_upwards [aνR] with x hx
    rw [integral_ker_pair L hok.1 hγ hmul w v v' ξ ξ' hx,
      hl _ (Submodule.subset_span ⟨_, hG.mul_mem _ hγ _ hx, rfl⟩) v hv,
      hl' _ (Submodule.subset_span ⟨_, hx, rfl⟩) v' hv']
    ext η
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul,
      inner_smul_left, inner_conj_symm]
    congr 1
    ring
  · filter_upwards [aν] with p hp
    exact integral_ker_group L hγ hmul hone huni aG hS' v v' ξ ξ' hp

end GlobalTheory.AmpOrb
