import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset

open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.SplitWeil NumberField
open GlobalTheory.AutomorphicL2Unitary (conv starFn hasCompactSupport_starFn)
open scoped Topology ComplexConjugate ContDiff Manifold

noncomputable section

namespace GlobalTheory.Orb

section Param

theorem contDiff_integral_param {H X P : Type} [TopologicalSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
    [T2Space H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup P] [NormedSpace ℝ P] {k : H → X} (hk : Continuous k) {φ : H → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {Ψ : P × X → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ ∞ fun p => ∫ x, φ x * Ψ (p, k x) ∂μ := by
  borelize X
  let e : H → X × ℂ := fun x => (k x, φ x)
  have he : Continuous e := hk.prodMk hφ
  obtain ⟨R, hR0, hR⟩ := (hc.isCompact.image he).isBounded.subset_closedBall_lt 0 0
  let χ : ContDiffBump (0 : X × ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  have : IsFiniteMeasure (μ.restrict (tsupport φ)) := isFiniteMeasure_restrict.2 hc.isCompact.measure_ne_top
  have hg : ContDiff ℝ ∞ fun q : P × (X × ℂ) => (χ (-q.2) : ℂ) * ((-q.2).2 * Ψ (q.1, (-q.2).1)) :=
    (Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd.neg)).mul
      (contDiff_snd.neg.snd.mul (hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg.fst)))
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (ContinuousLinearMap.mul ℝ ℂ) (s := (univ : Set P)) (v := fun _ => (0 : X × ℂ)) contDiffOn_const
    (f := fun _ => (1 : ℂ)) (μ := (μ.restrict (tsupport φ)).map e)
    (g := fun p z => (χ (-z) : ℂ) * ((-z).2 * Ψ (p, (-z).1)))
    (k := Metric.closedBall 0 (R + 1)) isOpen_univ (isCompact_closedBall _ _) ?_
    (integrable_const _).locallyIntegrable hg.contDiffOn
  · rw [contDiffOn_univ] at key
    convert key using 2 with p
    rw [convolution_def, integral_map he.aemeasurable, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := tsupport φ) fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]]
    · refine setIntegral_congr_fun (isClosed_tsupport φ).measurableSet fun x hx => ?_
      simp only [zero_sub, neg_neg, ContinuousLinearMap.mul_apply']
      rw [χ.one_of_mem_closedBall (hR ⟨x, hx, rfl⟩)]
      simp [e]
    · exact (continuous_const.mul (hg.continuous.comp
        (continuous_const.prodMk (continuous_const.sub continuous_id)))).aestronglyMeasurable
  · intro p z _ hz
    have : χ (-z) = 0 := by
      apply χ.zero_of_le_dist
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
      simpa [χ] using hz.le
    simp [this]

end Param

section Coord

variable {H X : Type} [Group H] [TopologicalSpace H] [NormedAddCommGroup X] [NormedSpace ℝ X]

def IsGroupCoord (c : H → X) : Prop :=
  Continuous c ∧ (∃ m : X × X → X, ContDiff ℝ ∞ m ∧ ∀ a b, c (a * b) = m (c a, c b)) ∧
    ∃ (U : Set X) (i : X → X), IsOpen U ∧ (∀ g, c g ∈ U) ∧ ContDiffOn ℝ ∞ i U ∧ ∀ g, c g⁻¹ = i (c g)

theorem IsGroupCoord.comp {H' : Type} [Group H'] [TopologicalSpace H'] {c : H → X} (h : IsGroupCoord c) (φ : H' →* H)
    (hφ : Continuous φ) : IsGroupCoord fun g => c (φ g) := by
  obtain ⟨h1, ⟨m, hm, em⟩, U, i, hU, hc, hi, ei⟩ := h
  exact ⟨h1.comp hφ, ⟨m, hm, fun a b => by simp only [map_mul, em]⟩, U, i, hU, fun g => hc _, hi,
    fun g => by simp only [map_inv, ei]⟩

theorem IsGroupCoord.pi {I : Type} [Fintype I] {Y : I → Type} [∀ j, NormedAddCommGroup (Y j)]
    [∀ j, NormedSpace ℝ (Y j)] {c : ∀ j, H → Y j} (h : ∀ j, IsGroupCoord (c j)) :
    IsGroupCoord fun g j => c j g := by
  choose m hm em using fun j => (h j).2.1
  choose U i hU hc hi ei using fun j => (h j).2.2
  refine ⟨continuous_pi fun j => (h j).1, ⟨fun p j => m j (p.1 j, p.2 j),
    contDiff_pi.2 fun j => (hm j).comp ((contDiff_pi.1 contDiff_fst j).prodMk (contDiff_pi.1 contDiff_snd j)),
    fun a b => funext fun j => em j a b⟩,
    univ.pi U, fun y j => i j (y j), isOpen_set_pi finite_univ fun j _ => hU j, fun g j _ => hc j g,
    contDiffOn_pi.2 fun j => (hi j).comp (contDiff_pi.1 contDiff_id j).contDiffOn fun y hy => hy j trivial,
    fun g => funext fun j => ei j g⟩

theorem contDiff_det_of_entries {n : Type} [Fintype n] [DecidableEq n] {A : X → Matrix n n ℂ}
    (h : ∀ i j, ContDiff ℝ ∞ fun y => A y i j) : ContDiff ℝ ∞ fun y => (A y).det := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_prod fun i _ => h _ _)

theorem isGroupCoord_matCoord {n : Type} [Fintype n] [DecidableEq n] {ι : H →* Matrix n n ℂ} (hι : Continuous ι) :
    IsGroupCoord (matCoord ι) := by
  have hd : ContDiff ℝ ∞ fun y : n → n → ℂ => (Matrix.of y).det :=
    contDiff_det_of_entries fun i j => by simp only [Matrix.of_apply]; fun_prop
  refine ⟨hι, ⟨fun p i j => ∑ k, p.1 i k * p.2 k j, by fun_prop, fun a b => ?_⟩,
    {y | (Matrix.of y).det ≠ 0}, fun y i j => ((Matrix.of y).det)⁻¹ * (Matrix.of y).adjugate i j,
    isOpen_ne_fun hd.continuous continuous_const, fun g => ?_, ?_, fun g => ?_⟩
  · funext i j
    simp [matCoord, Matrix.mul_apply]
  · exact (((Group.isUnit g).map ι).map Matrix.detMonoidHom).ne_zero
  · refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => (hd.contDiffOn.inv fun y hy => hy).mul
      (ContDiff.contDiffOn ?_)
    simp only [Matrix.adjugate_apply]
    refine contDiff_det_of_entries fun a b => ?_
    simp only [Matrix.updateRow_apply, Matrix.of_apply]
    split_ifs <;> fun_prop
  · funext i j
    have e : ι g⁻¹ = (ι g)⁻¹ := (Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])).symm
    change ι g⁻¹ i j = (ι g).det⁻¹ * (ι g).adjugate i j
    rw [e, Matrix.inv_def, Ring.inverse_eq_inv]
    rfl

variable [IsTopologicalGroup H] {c : H → X} {f f' : H → ℂ}

theorem IsGroupCoord.translate_mem (h : IsGroupCoord c) (hf : f ∈ CcSmooth c) (a b : H) :
    (fun g => f (a * g * b)) ∈ CcSmooth c := by
  obtain ⟨-, ⟨m, hm, em⟩, -⟩ := h
  obtain ⟨hc, Φ, hΦ, e⟩ := hf
  exact ⟨hc.comp_homeomorph ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight b)),
    fun y => Φ (m (m (c a, y), c b)), hΦ.comp (hm.comp ((hm.comp (by fun_prop)).prodMk contDiff_const)),
    fun g => by simp only [e, em]⟩

variable [FiniteDimensional ℝ X]

theorem IsGroupCoord.inv_mem (h : IsGroupCoord c) (hf : f ∈ CcSmooth c) : (fun g => f g⁻¹) ∈ CcSmooth c := by
  obtain ⟨h1, -, U, i, hU, hc, hi, ei⟩ := h
  obtain ⟨hs, Φ, hΦ, e⟩ := hf
  have hs' : HasCompactSupport fun g => f g⁻¹ := hs.comp_homeomorph (Homeomorph.inv H)
  obtain ⟨χ, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, X) (n := ⊤) hU.isClosed_compl
    (hs'.isCompact.image h1).isClosed (disjoint_left.2 fun y hy ⟨g, _, hg⟩ => hy (hg ▸ hc g))
  have hχ : ContDiff ℝ ∞ fun y => ((χ y : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp χ.contMDiff.contDiff
  refine ⟨hs', fun y => χ y * Φ (i y), contDiff_iff_contDiffAt.2 fun y => ?_, fun g => ?_⟩
  · by_cases hy : y ∈ U
    · exact hχ.contDiffAt.mul (hΦ.contDiffAt.comp y (hi.contDiffAt (hU.mem_nhds hy)))
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [h0.filter_mono (nhds_le_nhdsSet hy)] with z hz
      simp [hz]
  · simp only [← ei, ← e]
    by_cases hg : g ∈ tsupport fun g => f g⁻¹
    · rw [h1.self_of_nhdsSet _ ⟨g, hg, rfl⟩]; simp
    · have : f g⁻¹ = 0 := image_eq_zero_of_notMem_tsupport (f := fun g => f g⁻¹) hg
      simp [this]

theorem IsGroupCoord.starFn_mem (h : IsGroupCoord c) (hf : f ∈ CcSmooth c) : starFn f ∈ CcSmooth c := by
  obtain ⟨-, Φ, hΦ, e⟩ := h.inv_mem hf
  exact ⟨hasCompactSupport_starFn hf.1, fun y => conj (Φ y), Complex.conjCLE.contDiff.comp hΦ,
    fun g => congrArg conj (e g)⟩

variable [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ]

theorem IsGroupCoord.conv_mem_right (h : IsGroupCoord c) (hf : Continuous f) (hc : HasCompactSupport f)
    (hf' : f' ∈ CcSmooth c) : conv μ f f' ∈ CcSmooth c := by
  obtain ⟨h1, ⟨m, hm, em⟩, -⟩ := h
  obtain ⟨hc', Φ, hΦ, e⟩ := hf'
  refine ⟨hasCompactSupport_conv hc hc', _, contDiff_integral_param μ (h1.comp continuous_inv) hf hc
    (Ψ := fun q => Φ (m (q.2, q.1))) (hΦ.comp (hm.comp (by fun_prop))), fun g => ?_⟩
  simp only [conv, e, em, Function.comp]

theorem IsGroupCoord.conv_mem (h : IsGroupCoord c) (hf : f ∈ CcSmooth c) (hf' : f' ∈ CcSmooth c) :
    conv μ f f' ∈ CcSmooth c := h.conv_mem_right μ (continuous_of_mem_ccSmooth h.1 hf) hf.1 hf'

end Coord

section Mat

variable {H n : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Fintype n] [DecidableEq n]
  {ι : H →* Matrix n n ℂ} {f f' : H → ℂ}

variable [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [IsFiniteMeasureOnCompacts μ]

end Mat

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem translate_mem_SB {f : G → ℂ} (h : f ∈ SB G) (a b : G) : (fun g => f (a * g * b)) ∈ SB G :=
  comp_mem_SB h ((Homeomorph.mulLeft a).trans (Homeomorph.mulRight b))

variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem conv_add_left {f₁ f₂ f' : G → ℂ} (h₁ : Continuous f₁) (c₁ : HasCompactSupport f₁) (h₂ : Continuous f₂)
    (c₂ : HasCompactSupport f₂) (h' : Continuous f') : conv μ (f₁ + f₂) f' = conv μ f₁ f' + conv μ f₂ f' := by
  funext y
  have hy : Continuous fun x => f' (x⁻¹ * y) := h'.comp (by fun_prop)
  simp only [conv, Pi.add_apply, add_mul]
  exact integral_add ((h₁.mul hy).integrable_of_hasCompactSupport c₁.mul_right)
    ((h₂.mul hy).integrable_of_hasCompactSupport c₂.mul_right)

theorem conv_add_right {f f₁ f₂ : G → ℂ} (h : Continuous f) (c : HasCompactSupport f) (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) : conv μ f (f₁ + f₂) = conv μ f f₁ + conv μ f f₂ := by
  funext y
  have hy : Continuous fun x : G => x⁻¹ * y := by fun_prop
  simp only [conv, Pi.add_apply, mul_add]
  exact integral_add ((h.mul (h₁.comp hy)).integrable_of_hasCompactSupport c.mul_right)
    ((h.mul (h₂.comp hy)).integrable_of_hasCompactSupport c.mul_right)

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in

theorem conv_smul_smul (a b : ℂ) (f f' : G → ℂ) : conv μ (a • f) (b • f') = (a * b) • conv μ f f' := by
  funext y
  simp only [conv, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  exact integral_congr_ae (.of_forall fun x => by ring)

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isGroupCoord_archCoord (w : InfinitePlace F) : IsGroupCoord (archCoord σ J w) :=
  .pi fun τ => isGroupCoord_matCoord (continuous_archMat σ J τ)

theorem isGroupCoord_infCoord : IsGroupCoord (infCoord σ J) :=
  .pi fun w => (isGroupCoord_archCoord σ J w).comp (projInfArch σ J w) (continuous_projInfArch σ J w)

variable {σ J}

section Arch

variable {w : InfinitePlace F} {f f' : GArch σ J w → ℂ}

theorem starFn_mem_ccArch (hf : f ∈ CcArch σ J w) : starFn f ∈ CcArch σ J w :=
  (isGroupCoord_archCoord σ J w).starFn_mem hf

end Arch

section Inf

variable {f f' : GInf σ J → ℂ}

theorem starFn_mem_ccInf (hf : f ∈ CcInf σ J) : starFn f ∈ CcInf σ J :=
  (isGroupCoord_infCoord σ J).starFn_mem hf

end Inf

section Ad

omit [NumberField E] in

theorem starFn_infFin (a : GInf σ J → ℂ) (b : GFin σ J → ℂ) :
    starFn (infFin σ J a b) = infFin σ J (starFn a) (starFn b) := by
  funext g
  simp [starFn, infFin]

theorem exists_map_infFinEquiv_eq_prod (μ : Measure (GAd σ J)) [μ.IsHaarMeasure] :
    ∃ (μa : Measure (GInf σ J)) (μf : Measure (GFin σ J)), μa.IsHaarMeasure ∧ μf.IsHaarMeasure ∧
      μ.map (infFinEquiv σ J) = μa.prod μf := by
  have := (infFinEquiv σ J).isHaarMeasure_map μ
  let ν : Measure (GInf σ J × GFin σ J) := Measure.haar.prod Measure.haar
  refine ⟨Measure.haarScalarFactor (μ.map (infFinEquiv σ J)) ν • Measure.haar, Measure.haar,
    Measure.IsHaarMeasure.nnreal_smul _ (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', inferInstance, ?_⟩
  refine (Measure.isMulLeftInvariant_eq_smul _ ν).trans ?_
  exact (Measure.prod_smul_left _).symm

theorem conv_infFin {μ : Measure (GAd σ J)} {μa : Measure (GInf σ J)} {μf : Measure (GFin σ J)} [SFinite μa]
    [SFinite μf] (h : μ.map (infFinEquiv σ J) = μa.prod μf) (a a' : GInf σ J → ℂ) (b b' : GFin σ J → ℂ) :
    conv μ (infFin σ J a b) (infFin σ J a' b') = infFin σ J (conv μa a a') (conv μf b b') := by
  funext y
  simp only [conv, infFin]
  rw [← integral_prod_mul, ← h]
  refine Eq.trans ?_ ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.integral_map _).symm
  refine integral_congr_ae (.of_forall fun x => ?_)
  change _ = a (projInf σ J x) * a' ((projInf σ J x)⁻¹ * _) * (b (projFin σ J x) * b' ((projFin σ J x)⁻¹ * _))
  simp only [map_mul, map_inv]
  ring

variable {f f' : GAd σ J → ℂ}

theorem starFn_mem_ccAd (hf : f ∈ CcAd σ J) : starFn f ∈ CcAd σ J := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    exact starFn_infFin a b ▸ infFin_mem_ccAd (starFn_mem_ccInf ha) (starFn_mem_SB hb)
  | zero => convert (CcAd σ J).zero_mem using 1; funext g; simp [starFn]
  | add f f' _ _ h h' => convert (CcAd σ J).add_mem h h' using 1; funext g; simp [starFn]
  | smul a f _ h => convert (CcAd σ J).smul_mem (conj a) h using 1; funext g; simp [starFn]

theorem conv_mem_ccAd (μ : Measure (GAd σ J)) [μ.IsHaarMeasure] (hf : f ∈ CcAd σ J) (hf' : f' ∈ CcAd σ J) :
    conv μ f f' ∈ CcAd σ J := by
  obtain ⟨μa, μf, _, _, h⟩ := exists_map_infFinEquiv_eq_prod μ
  induction hf, hf' using Submodule.span_induction₂ with
  | mem_mem f f' hf hf' =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hf
    obtain ⟨a', ha', b', hb', rfl⟩ := hf'
    rw [conv_infFin h]
    exact infFin_mem_ccAd ((isGroupCoord_infCoord σ J).conv_mem μa ha ha') (conv_mem_SB hb hb')
  | zero_left f _ => convert (CcAd σ J).zero_mem using 1; funext g; simp [conv]
  | zero_right f _ => convert (CcAd σ J).zero_mem using 1; funext g; simp [conv]
  | add_left f₁ f₂ f' h₁ h₂ h' i₁ i₂ =>
    rw [conv_add_left μ (continuous_of_mem_ccAd h₁).1 (continuous_of_mem_ccAd h₁).2 (continuous_of_mem_ccAd h₂).1
      (continuous_of_mem_ccAd h₂).2 (continuous_of_mem_ccAd h').1]
    exact (CcAd σ J).add_mem i₁ i₂
  | add_right f f₁ f₂ h h₁ h₂ i₁ i₂ =>
    rw [conv_add_right μ (continuous_of_mem_ccAd h).1 (continuous_of_mem_ccAd h).2 (continuous_of_mem_ccAd h₁).1
      (continuous_of_mem_ccAd h₂).1]
    exact (CcAd σ J).add_mem i₁ i₂
  | smul_left r f f' _ _ i =>
    have := conv_smul_smul μ r 1 f f'
    rw [one_smul] at this
    exact this ▸ (CcAd σ J).smul_mem _ i
  | smul_right r f f' _ _ i =>
    have := conv_smul_smul μ 1 r f f'
    rw [one_smul] at this
    exact this ▸ (CcAd σ J).smul_mem _ i

end Ad

end GlobalTheory.Orb
