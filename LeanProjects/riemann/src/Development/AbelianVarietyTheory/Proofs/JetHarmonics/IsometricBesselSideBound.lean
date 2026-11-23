import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hc : 0 ≤ c) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal c ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← h]
    refine lintegral_congr fun x => ?_
    simp [enorm_eq_nnnorm]
  rw [h2, ← ENNReal.rpow_mul]
  norm_num

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ := by
  let L : S →ₗᵢ[ℂ] Lp F 2 μ :=
    { toFun := fun v => (hm v v.2).toLp (Φ v)
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd v v.2 w w.2)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c v v.2)
      norm_map' := fun v => by
        change ‖(hm v v.2).toLp (Φ v)‖ = _
        rw [Lp.norm_toLp, hn v v.2, ENNReal.toReal_ofReal (norm_nonneg _)]
        rfl }
  intro w hw w' hw'
  have h := L.inner_map_map ⟨w', hw'⟩ ⟨w, hw⟩
  rw [L2.inner_def] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae ?_
  filter_upwards [(hm w hw).coeFn_toLp, (hm w' hw').coeFn_toLp] with x h1 h2
  change _ = ⟪((hm w' hw').toLp (Φ w')) x, ((hm w hw).toLp (Φ w)) x⟫_ℂ
  rw [h1, h2]

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDS ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq Bm hDS hS hB
  obtain ⟨hae, -, -, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hDS hS
  obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hDS
  have hn : ∀ w ∈ R.sm, eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq =
      ENNReal.ofReal ‖w‖ := fun w hw =>
    eLpNorm_two_of_lintegral_sq _ _ (norm_nonneg _) (hB.2 w hw)
  have hm : ∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq := fun w hw =>
    ⟨hmeas Bm hB.1 w hw, by rw [hn w hw]; exact ENNReal.ofReal_lt_top⟩
  refine ⟨hm, ?_⟩
  refine integral_inner_of_isometric R.smSub
    (fun w (x : Formalism.QuantumDeterminants.Mt k r) => Bm (R.σ (Matrix.of x) w)) hm hn ?_ ?_
  · intro v hv w hw
    filter_upwards [hae] with x hx
    simp only [Pi.add_apply, map_add]
    exact hB.1.1 _ (hsm _ hx v hv) _ (hsm _ hx w hw)
  · intro c v hv
    filter_upwards [hae] with x hx
    simp only [Pi.smul_apply, map_smul]
    exact hB.1.2.1 c _ (hsm _ hx v hv)

end GlobalTheory
