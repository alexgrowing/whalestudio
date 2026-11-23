import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramChartSubFormEntryLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SaturationClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in

def adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (τ : Ψ) (a c : Fin r) : ℂ :=
  (Matrix.adjugate (mat k τ) * mat w τ) a c

omit [NumberField E] [IsCMField E] in
theorem lact_lact {Ψ : Finset (E →+* ℂ)} (a b : GL (Fin r) E) (x : Frame Ψ r) :
    lact a (lact b x) = lact (a * b) x := by
  funext τ
  show ((a : Matrix (Fin r) (Fin r) E).map τ.1 * ((b : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) :
    Matrix (Fin r) (Fin r) ℂ) = (((a * b : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ)
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

omit [NumberField E] [IsCMField E] in
theorem lact_one {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) : lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]; rfl

omit [NumberField E] [IsCMField E] in

theorem adjEnt_rmul {Ψ : Finset (E →+* ℂ)} (k b : Frame Ψ r) (hb : b ∈ Bor Ψ r) (τ : Ψ) (a c : Fin r)
    (hca : c < a) : adjEnt k (rmul k b) τ a c = 0 := by
  have h1 : mat (rmul k b) τ = mat k τ * mat b τ := rfl
  rw [adjEnt, h1, ← Matrix.mul_assoc, Matrix.adjugate_mul]
  simp [Matrix.smul_mul, mat, (hb τ).2 a c hca]

omit [NumberField E] [IsCMField E] in

theorem exists_of_adjEnt {Ψ : Finset (E →+* ℂ)} (k w : Frame Ψ r) (hk : ∀ τ, (mat k τ).det ≠ 0)
    (hw : ∀ τ, (mat w τ).det ≠ 0) (h0 : ∀ τ a c, c < a → adjEnt k w τ a c = 0) :
    ∃ b ∈ Bor Ψ r, w = rmul k b := by
  refine ⟨fun τ => ((mat k τ)⁻¹ * mat w τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · show ((mat k τ)⁻¹ * mat w τ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (inv_ne_zero (hk τ)) (hw τ)
  · show ((mat k τ)⁻¹ * mat w τ) a c = 0
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply]
    have := h0 τ a c hca
    rw [adjEnt] at this
    rw [this, smul_zero]
  · funext τ
    show mat w τ = mat k τ * ((mat k τ)⁻¹ * mat w τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hk τ))]

omit [NumberField E] [IsCMField E] in
theorem continuous_mat {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f : α → Frame Ψ r}
    (hf : Continuous f) (τ : Ψ) : Continuous fun p => mat (f p) τ :=
  (continuous_apply τ).comp hf

omit [NumberField E] [IsCMField E] in
theorem continuous_lact {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) :
    Continuous (lact (Ψ := Ψ) γ) := by
  refine continuous_pi fun τ => ?_
  exact continuous_const.matrix_mul (continuous_mat continuous_id τ)

omit [NumberField E] [IsCMField E] in
theorem continuous_adjEnt {α : Type} [TopologicalSpace α] {Ψ : Finset (E →+* ℂ)} {f g : α → Frame Ψ r}
    (hf : Continuous f) (hg : Continuous g) (τ : Ψ) (a c : Fin r) :
    Continuous fun p => adjEnt (f p) (g p) τ a c :=
  (((continuous_mat hf τ).matrix_adjugate).matrix_mul (continuous_mat hg τ)).matrix_elem a c

theorem eventually_not_mem_saturation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ), (∀ z : V (nd X), ‖z‖ ≤ ρ → z ∈ OmF X x) →
    ∀ y ∈ X.dom, (¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y = lact γ (rmul (cpt X x z) b)) →
    ∀ᶠ y' in 𝓝 y, ¬ ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z : V (nd X), ‖z‖ ≤ ρ ∧
      y' = lact γ (rmul (cpt X x z) b) := by
  intro E _ _ _ r X x ρ hΩ y hy hny
  have hcpt : Continuous (cpt X x) := (GlobalTheory.InterpCompare.differentiable_chart X x).continuous
  have hK : IsCompact (Metric.closedBall (0 : V (nd X)) ρ) := isCompact_closedBall 0 ρ
  have key : ∀ z ∈ Metric.closedBall (0 : V (nd X)) ρ, ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
      ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, p.1 ≠ lact γ (rmul (cpt X x p.2) b) := by
    intro z hz
    have hz' : ‖z‖ ≤ ρ := by simpa using hz
    have hk : cpt X x z ∈ X.dom := hΩ z hz'
    obtain ⟨U, hU, U', hU', hfin⟩ := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X y hy _ hk
    have h1 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z), p.1 ∈ U ∧ cpt X x p.2 ∈ U' := by
      refine Filter.Eventually.and (continuous_fst.continuousAt.preimage_mem_nhds hU) ?_
      exact (hcpt.comp continuous_snd).continuousAt.preimage_mem_nhds hU'
    have h2 : ∀ᶠ p : Frame X.Ψ r × V (nd X) in 𝓝 (y, z),
        ∀ δ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b},
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0 := by
      refine (Filter.eventually_all_finite hfin).2 fun δ hδ => ?_
      have hopen : IsOpen {p : Frame X.Ψ r × V (nd X) |
          ∃ τ : X.Ψ, ∃ a c : Fin r, c < a ∧ adjEnt (cpt X x p.2) (lact δ p.1) τ a c ≠ 0} := by
        simp only [Set.setOf_exists]
        refine isOpen_iUnion fun τ => isOpen_iUnion fun a => isOpen_iUnion fun c => ?_
        by_cases hca : c < a
        · simp only [hca, true_and]
          exact isOpen_ne_fun (continuous_adjEnt (hcpt.comp continuous_snd)
            ((continuous_lact δ).comp continuous_fst) τ a c) continuous_const
        · simp [hca]
      refine hopen.mem_nhds ?_
      by_contra hcon
      simp only [Set.mem_setOf_eq, not_exists, not_and, not_not] at hcon
      have hdk : ∀ τ, (mat (cpt X x z) τ).det ≠ 0 := fun τ => (hk τ).1
      have hdw : ∀ τ, (mat (lact δ y) τ).det ≠ 0 := by
        intro τ h0
        have e : y = lact δ⁻¹ (lact δ y) := by rw [lact_lact, inv_mul_cancel, lact_one]
        have : (mat y τ).det = 0 := by
          rw [e]
          show (((δ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat (lact δ y) τ).det = 0
          rw [Matrix.det_mul, h0, mul_zero]
        exact (hy τ).1 this
      obtain ⟨b, hb, hwb⟩ := exists_of_adjEnt _ _ hdk hdw hcon
      refine hny ⟨δ⁻¹, X.Γ.inv_mem hδ.1, b, hb, z, hz', ?_⟩
      rw [← hwb, lact_lact, inv_mul_cancel, lact_one]
    filter_upwards [h1, h2] with p hp1 hp2
    intro γ hγ b hb he
    have hδ : γ⁻¹ ∈ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ u ∈ U, ∃ u' ∈ U', ∃ b ∈ Bor X.Ψ r, lact γ u = rmul u' b} := by
      refine ⟨X.Γ.inv_mem hγ, p.1, hp1.1, cpt X x p.2, hp1.2, b, hb, ?_⟩
      rw [he, lact_lact, inv_mul_cancel, lact_one]
    obtain ⟨τ, a, c, hca, hne⟩ := hp2 _ hδ
    apply hne
    rw [he, lact_lact, inv_mul_cancel, lact_one]
    exact adjEnt_rmul _ _ hb τ a c hca
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun y' z => ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, y' ≠ lact γ (rmul (cpt X x z) b)) key] with y' hy'
  rintro ⟨γ, hγ, b, hb, z, hz, he⟩
  exact hy' z (by simpa using hz) γ hγ b hb he

end GlobalTheory.SaturationClosed
