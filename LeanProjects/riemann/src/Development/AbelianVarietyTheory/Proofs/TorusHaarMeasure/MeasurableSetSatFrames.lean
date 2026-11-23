import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Unfold

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def satFrames (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X))) : Set (Frame X.Ψ r) :=
  {x | ∃ z ∈ A, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x0 z) b}

theorem measurableSet_Bor (X : Data E r) : MeasurableSet (Bor X.Ψ r) := by
  have h : Bor X.Ψ r = ⋂ τ : X.Ψ, ({b : Frame X.Ψ r | (mat b τ).det ≠ 0} ∩
      ⋂ a : Fin r, ⋂ c : Fin r, ⋂ (_ : c < a), {b : Frame X.Ψ r | b τ a c = 0}) := by
    ext b; simp [Bor]
  rw [h]
  refine MeasurableSet.iInter fun τ => MeasurableSet.inter ?_ ?_
  · have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
    exact (isOpen_ne_fun hM.matrix_det continuous_const).measurableSet
  · refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet

theorem continuous_rmul (X : Data E r) :
    Continuous fun p : Frame X.Ψ r × Frame X.Ψ r => rmul p.1 p.2 := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact (hM.comp continuous_fst).matrix_mul (hM.comp continuous_snd)

theorem continuous_lact (X : Data E r) (γ : GL (Fin r) E) :
    Continuous fun x : Frame X.Ψ r => lact γ x := by
  refine continuous_pi fun τ => ?_
  have hM : Continuous fun b : Frame X.Ψ r => mat b τ := continuous_apply τ
  exact continuous_const.matrix_mul hM

theorem rmul_right_cancel (X : Data E r) {y b b' : Frame X.Ψ r} (hy : y ∈ X.dom)
    (h : rmul y b = rmul y b') : b = b' := by
  funext τ
  have h1 : mat y τ * mat b τ = mat y τ * mat b' τ := congrFun h τ
  have hu : IsUnit (mat y τ).det := isUnit_iff_ne_zero.mpr (hy τ).1
  have := congrArg (fun M => (mat y τ)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hu] at this
  exact this

theorem measurableSet_satFrames (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {A : Set (V (nd X))} (hA : MeasurableSet A) (hAO : A ⊆ OmF X x0) :
    MeasurableSet (satFrames X x0 A) := by
  have h : satFrames X x0 A =
      (fun p : V (nd X) × Frame X.Ψ r => rmul (cpt X x0 p.1) p.2) '' (A ×ˢ Bor X.Ψ r) := by
    ext x
    constructor
    · rintro ⟨z, hz, b, hb, rfl⟩; exact ⟨(z, b), ⟨hz, hb⟩, rfl⟩
    · rintro ⟨⟨z, b⟩, ⟨hz, hb⟩, rfl⟩; exact ⟨z, hz, b, hb, rfl⟩
  rw [h]
  have : PolishSpace (Fin r → ℂ) := inferInstance
  have : PolishSpace (Fin r → Fin r → ℂ) := inferInstance
  have : PolishSpace (Frame X.Ψ r) := inferInstance
  have : PolishSpace (V (nd X)) := inferInstance
  refine MeasurableSet.image_of_continuousOn_injOn (hA.prod (measurableSet_Bor X)) ?_ ?_
  · exact ((continuous_rmul X).comp (((FundSetPf.cont_cpt X x0).comp continuous_fst).prodMk
      continuous_snd)).continuousOn
  · rintro ⟨z, b⟩ ⟨hz, hb⟩ ⟨z', b'⟩ ⟨-, hb'⟩ hh
    obtain rfl : z = z' := FundSetPf.cpt_uniq X ho hb hb' hh
    exact Prod.ext rfl (rmul_right_cancel X (hAO hz) hh)

theorem rmul_mem_satFrames_iff (X : Data E r) (x0 : Frame X.Ψ r) (A : Set (V (nd X)))
    (x : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ satFrames X x0 A ↔ x ∈ satFrames X x0 A := by
  constructor
  · rintro ⟨z, hz, b', hb', h⟩
    refine ⟨z, hz, rmul b' (ExtFPf.invF X b), ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb), ?_⟩
    rw [← ExtFPf.rmul_assoc, ← h, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  · rintro ⟨z, hz, b', hb', rfl⟩
    exact ⟨z, hz, rmul b' b, ExtFPf.mul_mem X hb' hb, by rw [ExtFPf.rmul_assoc]⟩

theorem cpt_mem_satFrames_iff (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    (A : Set (V (nd X))) (z : V (nd X)) : cpt X x0 z ∈ satFrames X x0 A ↔ z ∈ A := by
  constructor
  · rintro ⟨z', hz', b, hb, h⟩
    rw [← ExtFPf.rmul_oneF X (cpt X x0 z)] at h
    rw [FundSetPf.cpt_uniq X ho (ExtFPf.oneF_mem X) hb h]; exact hz'
  · intro hz
    exact ⟨z, hz, ExtFPf.oneF X, ExtFPf.oneF_mem X, (ExtFPf.rmul_oneF X _).symm⟩

theorem cpt_lact (X : Data E r) (x0 : Frame X.Ψ r) (γ : GL (Fin r) E) (z : V (nd X)) :
    cpt X (lact γ x0) z = lact γ (cpt X x0 z) := (FundSetPf.lact_rmul γ _ _).symm

theorem isOrth_lact (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) : IsOrth X (lact γ x0) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

theorem muF_lact (X : Data E r) (x0 : Frame X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) :
    muF X (lact γ x0) = muF X x0 := by
  have h1 : OmF X (lact γ x0) = OmF X x0 := by
    ext z
    show cpt X (lact γ x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
    rw [cpt_lact]
    refine ⟨fun h => ?_, OntoS.dom_lact X hγ⟩
    have := OntoS.dom_lact X (X.Γ.inv_mem hγ) h
    rwa [FundSetPf.lact_inv] at this
  have h2 : densF X (lact γ x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_lact, OntoS.gram_lact X hγ]
  simp only [muF, h1, h2]

theorem unique_translate (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) {x : Frame X.Ψ r} {γ γ' : GL (Fin r) E} (hγ : γ ∈ X.Γ) (hγ' : γ' ∈ X.Γ)
    (h : lact γ⁻¹ x ∈ satFrames X x0 FF) (h' : lact γ'⁻¹ x ∈ satFrames X x0 FF) : γ = γ' := by
  obtain ⟨z, hz, b, hb, h⟩ := h
  obtain ⟨z', hz', b', hb', h'⟩ := h'
  have hδ : γ'⁻¹ * γ ∈ X.Γ := X.Γ.mul_mem (X.Γ.inv_mem hγ') hγ
  have e1 : lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) b) = rmul (cpt X x0 z') b' := by
    rw [← h, ← h', ← FundSetPf.lact_mul, mul_assoc, mul_inv_cancel, mul_one]
  have hbb := ExtFPf.mul_mem X hb (ExtFPf.invF_mem X hb')
  have e2 : cpt X x0 z' = lact (γ'⁻¹ * γ) (rmul (cpt X x0 z) (rmul b (ExtFPf.invF X b'))) := by
    rw [← ExtFPf.rmul_assoc, FundSetPf.lact_rmul, e1, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb',
      ExtFPf.rmul_oneF]
  obtain rfl : z = z' := hF.2.2.1 z hz z' hz' _ hδ _ hbb e2
  have e3 : lact (γ'⁻¹ * γ) (cpt X x0 z) = rmul (cpt X x0 z) (rmul b' (ExtFPf.invF X b)) := by
    rw [← ExtFPf.rmul_assoc, ← e1, ← FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb,
      ExtFPf.rmul_oneF]
  have := X.Γ_free _ hδ _ (hF.2.1 hz) _ (ExtFPf.mul_mem X hb' (ExtFPf.invF_mem X hb)) e3
  exact (inv_mul_eq_one.mp this).symm

theorem lintegral_unfold (hM : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (ho : IsOrth X x0) (FF : Set (V (nd X))) (hF : IsFundSet X x0 FF) (ψ : Frame X.Ψ r → ℝ≥0∞)
    (hψ : Measurable ψ) (hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) :
    ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hS := measurableSet_satFrames X ho hF.1 hF.2.1
  have hc : Measurable (cpt X x0) := (FundSetPf.cont_cpt X x0).measurable
  let φ : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ =>
    ((fun x => lact (γ.1)⁻¹ x) ⁻¹' satFrames X x0 FF).indicator ψ
  have hφm : ∀ γ, Measurable (φ γ) := fun γ =>
    hψ.indicator ((continuous_lact X _).measurable hS)
  have hφB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ γ (rmul x b) = φ γ x := by
    intro γ x hx b hb
    simp only [φ, Set.indicator, Set.mem_preimage, FundSetPf.lact_rmul,
      rmul_mem_satFrames_iff X x0 FF _ hb, hB x hx b hb]
  have h1 : ∀ᵐ z ∂muF X x0, ψ (cpt X x0 z) = ∑' γ : X.Γ, φ γ (cpt X x0 z) := by
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    have hm : lact γ⁻¹ (cpt X x0 z) ∈ satFrames X x0 FF :=
      ⟨z', hz', b, hb, by rw [h, FundSetPf.lact_inv]⟩
    rw [tsum_eq_single (⟨γ, hγ⟩ : X.Γ)]
    · exact (Set.indicator_of_mem (s := (fun x => lact γ⁻¹ x) ⁻¹' satFrames X x0 FF) hm ψ).symm
    · intro γ' hne
      refine Set.indicator_of_notMem (fun hm' => hne ?_) ψ
      exact Subtype.ext (unique_translate X hF γ'.2 hγ hm' hm)
  rw [lintegral_congr_ae h1,
    lintegral_tsum (f := fun γ z => φ γ (cpt X x0 z)) fun γ => ((hφm γ).comp hc).aemeasurable,
    lintegral_tsum (f := fun (γ : X.Γ) z => ψ (lact γ.1 (cpt X x0 z))) fun γ : X.Γ =>
      ((hψ.comp (continuous_lact X γ.1).measurable).comp hc).aemeasurable]
  refine tsum_congr fun γ => ?_
  rw [hM r X x0 (lact γ.1 x0) ho (isOrth_lact X ho γ.2) (φ γ) (hφm γ) (hφB γ), muF_lact X x0 γ.2,
    ← lintegral_indicator hF.1]
  refine lintegral_congr fun z => ?_
  simp only [φ, Set.indicator, Set.mem_preimage, cpt_lact, FundSetPf.lact_inv,
    cpt_mem_satFrames_iff X ho]

end GlobalTheory.Unfold
