import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.KU

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem countable_Γ (X : Data E r) : Countable X.Γ := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := (Units.val : GL (Fin r) E → Matrix (Fin r) (Fin r) E)) (fun _ _ h => Units.ext h)
  infer_instance

def Hg (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) (φ : Frame X.Ψ r → ℝ≥0∞)
    (γ : GL (Fin r) E) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  (lact γ⁻¹ ⁻¹' Sset X x0 FF).indicator (fun y => ENNReal.ofReal (kap X x0 bb y) * φ y) x

theorem meas_Hg (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : MeasurableSet FF) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞} (hφ : Measurable φ) (γ : GL (Fin r) E) :
    Measurable (Hg X x0 FF bb φ γ) :=
  ((meas_kap X x0 bb).ennreal_ofReal.mul hφ).indicator ((cont_lact X γ⁻¹).measurable (meas_S X ho hFF))

theorem Hg_rmul (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (bb : ℝ) {φ : Frame X.Ψ r → ℝ≥0∞}
    (hφB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) (γ : GL (Fin r) E) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    Hg X x0 FF bb φ γ (rmul x b) = Hg X x0 FF bb φ γ x := by
  classical
  simp only [Hg, Set.indicator_apply, Set.mem_preimage, lact_rmul', rmul_mem_S X hb,
    kap_rmul X x0 x bb hb, hφB x hx b hb]

private lemma lact_inv_lact_self {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  funext τ
  have h : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (γ : Matrix (Fin r) (Fin r) E) = 1 := by
    simp
  show ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * Matrix.of (x τ)) = x τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero τ.1) (map_one τ.1),
    Matrix.one_mul]
  rfl

theorem Hg_lact_cpt (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (FF : Set (V (nd X))) (bb : ℝ)
    {φ : Frame X.Ψ r → ℝ≥0∞} (hφΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) {γ : GL (Fin r) E}
    (hγ : γ ∈ X.Γ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Hg X x0 FF bb φ γ (lact γ (cpt X x0 z)) =
      FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ (cpt X x0 z))) * φ (cpt X x0 z)) z := by
  classical
  rw [Hg, Set.indicator_apply, Set.mem_preimage, lact_lact, inv_mul_cancel, lact_one, cpt_mem_S X ho,
    hφΓ γ hγ _ hz, Set.indicator_apply]

theorem cover (X : Data E r) {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hFF : IsFundSet X x0 FF) :
    ∀ᵐ z ∂muF X x0, ∃ γ ∈ X.Γ, lact γ⁻¹ (cpt X x0 z) ∈ Sset X x0 FF := by
  obtain ⟨-, -, -, h⟩ := hFF
  filter_upwards [h] with z hz
  obtain ⟨z', hz', γ, hγ, b, hb, he⟩ := hz
  exact ⟨γ, hγ, ⟨(z', b), ⟨hz', hb⟩, by rw [he, lact_inv_lact_self]⟩⟩

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := by
  intro r X x0 ho hPD FF hFF bb hbb
  obtain ⟨C, hC, hCb⟩ := sum_bound hSB X ho hPD bb hbb
  have := countable_Γ X
  refine ⟨C, hC, fun φ hφ hφB hφΓ => ?_⟩
  have hae : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 := ExtFPf.ae_OmF (X := X) (x0 := x0)
  have hT := (cont_cpt X x0).measurable
  have hI : ∀ γ : X.Γ, Measurable fun z => FF.indicator
      (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) * φ (cpt X x0 z)) z := fun γ =>
    ((meas_kap X x0 bb).comp ((cont_lact X γ.1).comp (cont_cpt X x0)).measurable).ennreal_ofReal.mul
      (hφ.comp hT) |>.indicator hFF.1
  have step1 : ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae ((hae.and (cover X hFF)).mono fun z ⟨hz, γ, hγ, hS⟩ => ?_)
    rw [kaF_eq X ho bb hz]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (⟨γ, hγ⟩ : X.Γ))
    rw [Hg, Set.indicator_of_mem (show cpt X x0 z ∈ lact γ⁻¹ ⁻¹' Sset X x0 FF from hS)]
  have step2 : ∫⁻ z, ∑' γ : X.Γ, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((meas_Hg X ho hFF.1 bb hφ γ.1).comp hT).aemeasurable
  have step3 : ∀ γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := by
    intro γ
    rw [hMI r X x0 (lact γ.1 x0) ho (isOrth_lact X γ.2 ho) (Hg X x0 FF bb φ γ.1)
      (meas_Hg X ho hFF.1 bb hφ γ.1) (fun x hx b hb => Hg_rmul X x0 FF bb hφB γ.1 hx hb),
      muF_lact X γ.2]
    refine lintegral_congr_ae (hae.mono fun z hz => ?_)
    show Hg X x0 FF bb φ γ.1 (cpt X (lact γ.1 x0) z) = _
    rw [cpt_lact, Hg_lact_cpt X ho FF bb hφΓ γ.2 hz]
  have step4 : ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator hFF.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ FF
    · simp only [Set.indicator_of_mem hz]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (hCb z (hFF.2.1 hz)) _
    · simp [Set.indicator_of_notMem hz]
  calc ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0
      ≤ ∑' γ : X.Γ, ∫⁻ z, Hg X x0 FF bb φ γ.1 (cpt X x0 z) ∂muF X x0 := step1.trans_eq step2
    _ = ∑' γ : X.Γ, ∫⁻ z, FF.indicator (fun z => ENNReal.ofReal (kap X x0 bb (lact γ.1 (cpt X x0 z))) *
        φ (cpt X x0 z)) z ∂muF X x0 := tsum_congr step3
    _ ≤ ∫⁻ z in FF, C * φ (cpt X x0 z) ∂muF X x0 := step4
    _ = C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0 := lintegral_const_mul C (hφ.comp hT)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.KU

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem kaUnfold_of (hMI : MeasInvStatement (E := E)) (hSB : SumBoundStatement) :
    KaUnfoldStatement (E := E) := KU.kaUnfold_of hMI hSB

end ReciprocityTheory.ChartRestriction.G.AR.Up
