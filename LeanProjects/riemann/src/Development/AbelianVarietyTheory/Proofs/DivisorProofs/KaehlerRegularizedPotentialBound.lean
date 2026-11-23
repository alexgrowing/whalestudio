import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps

set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory
open Filter Topology

namespace GlobalTheory.RegNullSet

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

theorem isRegConst_congr {a θ : ChartForm p σ d} {Ψ Ψ' : CxPts p σ → ℝ → ℝ} {A K δ t₀ : ℝ} (h₀ : 0 < t₀)
    (e : ∀ y t, 0 < t → t ≤ t₀ → Ψ' y t = Ψ y t) (h : IsRegConst a θ Ψ A K δ) : IsRegConst a θ Ψ' A K (min δ t₀) where
  A_nonneg := h.A_nonneg
  K_nonneg := h.K_nonneg
  δ_pos := lt_min h.δ_pos h₀
  smooth c := ((h.smooth c).mono (Set.prod_mono subset_rfl fun _ hw => ⟨hw.1, hw.2.trans_le (min_le_left _ _)⟩)).congr
    fun _ hq => e _ _ hq.2.1 (hq.2.2.le.trans (min_le_right _ _))
  mono y := ((h.mono y).mono (Ioo_subset_Ioo_right (min_le_left _ _))).congr
    fun t ht => by simp only [e y t ht.1 (ht.2.le.trans (min_le_right _ _))]
  hess c y hy w hw hw' ξ η := by
    have h₁ : ‖w‖ < t₀ := hw'.trans_le (min_le_right _ _)
    have e₁ : (fun t => Ψ' y t + K * t ^ 2) =ᶠ[𝓝 ‖w‖] fun t => Ψ y t + K * t ^ 2 := by
      filter_upwards [Ioo_mem_nhds hw h₁] with t ht
      rw [e y t ht.1 ht.2.le]
    have e₂ : (fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => Ψ' (c.e.symm q.1) ‖q.2‖) =ᶠ[𝓝 (c.e y, w)]
        fun q => Ψ (c.e.symm q.1) ‖q.2‖ := by
      have hc : Continuous fun q : ReciprocityTheory.L2DbarEstimates.V d × ℂ => ‖q.2‖ := by fun_prop
      filter_upwards [(hc.tendsto (c.e y, w)).eventually (Ioo_mem_nhds hw h₁)] with q hq
      exact e _ _ hq.1 hq.2.le
    rw [e₁.deriv_eq, leviForm_congr e₂]
    exact h.hess c y hy w hw (hw'.trans_le (min_le_left _ _)) ξ η

variable [SmoothOfRelativeDimension d p] {a : ChartForm p σ d} {E : ChartMap p σ d} {ψ g : CxPts p σ → ℝ}
  {B : Set (CxPts p σ)}

theorem exists_nhds_rho_eq (hK : KernelSt) (ha : IsKaehlerForm (AnRead.all p σ d) a) (hE : IsExph a E)
    (hB : ∀ y, y ∉ B → ψ y = g y) (h0 : ∀ c : AlgChart p σ d, volume (c.e '' (B ∩ c.e.source)) = 0) (x : CxPts p σ) :
    ∃ U ∈ 𝓝 x, ∃ t₀ > (0 : ℝ), ∀ y ∈ U, ∀ t, 0 < t → t ≤ t₀ → rho a E ψ y t = rho a E g y t := by
  obtain ⟨c, hx⟩ := AlgChart.exists_mem_source (D := d) x
  obtain ⟨r, hr, hs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (c.e.open_target.mem_nhds (c.e.map_source hx))
  obtain ⟨C, t₀, -, ht₀, H⟩ := hK k Y p σ d a E ha hE c _ (isCompact_closedBall _ r) hs
  refine ⟨c.e.source ∩ c.e ⁻¹' Metric.closedBall (c.e x) r, inter_mem (c.e.open_source.mem_nhds hx)
    (c.e.continuousAt hx (Metric.closedBall_mem_nhds _ hr)), t₀, ht₀, fun y hy t ht ht' => ?_⟩
  obtain ⟨h₁, -, h₂⟩ := H y hy.1 hy.2 t ht ht'
  have z : (fun v => |ψ (c.e.symm v) - g (c.e.symm v)|) =ᵐ[volume.restrict (Metric.ball (c.e y) (C * t))] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae (compl_mem_ae_iff.2 (h0 c))] with v hv hv'
    rw [hB _ fun hb => hv' ⟨_, ⟨hb, c.e.map_target (h₁ hv)⟩, c.e.right_inv (h₁ hv)⟩, sub_self, abs_zero]
    rfl
  obtain ⟨h₃, h₄⟩ := h₂ (fun y => |ψ y - g y|) ((integrable_zero _ _ _).congr z.symm)
  simp only [abs_abs] at h₄
  rw [integral_congr_ae z, integral_zero', mul_zero, abs_nonpos_iff, rho_eq ha hE _ hy.1, rhoIn, ChernReg.mean,
    div_eq_zero_iff, or_iff_left (mass_pos (continuous_and_smul ha hy.1).1 (continuous_and_smul ha hy.1).2
      (ha.2 _ y hy.1)).ne', integral_eq_zero_iff_of_nonneg
      (fun ξ => mul_nonneg (abs_nonneg _) (cutoff_nonneg _)) h₃] at h₄
  rw [rho_eq ha hE _ hy.1, rho_eq ha hE _ hy.1, rhoIn, rhoIn, ChernReg.mean, ChernReg.mean]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h₄] with ξ hξ
  rcases mul_eq_zero.1 hξ with h | h
  · rw [sub_eq_zero.1 (abs_eq_zero.1 h)]
  · rw [h, mul_zero, mul_zero]

theorem exists_rho_eq [CompactSpace (CxPts p σ)] (hK : KernelSt) (ha : IsKaehlerForm (AnRead.all p σ d) a)
    (hE : IsExph a E) (hB : ∀ y, y ∉ B → ψ y = g y)
    (h0 : ∀ c : AlgChart p σ d, volume (c.e '' (B ∩ c.e.source)) = 0) :
    ∃ t₀ > (0 : ℝ), ∀ y ∈ (univ : Set (CxPts p σ)), ∀ t, 0 < t → t ≤ t₀ → rho a E ψ y t = rho a E g y t := by
  refine isCompact_univ.induction_on
    (p := fun U => ∃ t₀ > (0 : ℝ), ∀ y ∈ U, ∀ t, 0 < t → t ≤ t₀ → rho a E ψ y t = rho a E g y t)
    ⟨1, one_pos, fun _ h => h.elim⟩ (fun _ _ hs ⟨t₀, h, H⟩ => ⟨t₀, h, fun y hy => H y (hs hy)⟩)
    (fun _ _ ⟨t₀, h, H⟩ ⟨t₁, h', H'⟩ => ⟨min t₀ t₁, lt_min h h', fun y hy t ht ht' =>
      hy.elim (fun hy => H y hy t ht (ht'.trans (min_le_left _ _))) fun hy => H' y hy t ht (ht'.trans (min_le_right _ _))⟩)
    fun x _ => ?_
  obtain ⟨U, hU, h⟩ := exists_nhds_rho_eq hK ha hE hB h0 x
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, h⟩

end GlobalTheory.RegNullSet

namespace GlobalTheory.RegNullSet

theorem transfer : KernelSt → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p], CompactSpace (CxPts p σ) → ∀ (a θ : ChartForm p σ d) (E : ChartMap p σ d) (ψ g : CxPts p σ → ℝ) (B : Set (CxPts p σ)), IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → (∀ y, y ∉ B → ψ y = g y) → (∀ c : AlgChart p σ d, MeasureTheory.volume (c.e '' (B ∩ c.e.source)) = 0) → ∀ A K δ : ℝ, IsRegConst a θ (rho a E g) A K δ → ∃ δ' : ℝ, IsRegConst a θ (rho a E ψ) A K δ' := by
  intro hK k _ Y p σ d _ _ a θ E ψ g B ha hE hB h0 A K δ h
  obtain ⟨t₀, h₀, e⟩ := exists_rho_eq hK ha hE hB h0
  exact ⟨_, isRegConst_congr h₀ (fun y => e y trivial) h⟩

end GlobalTheory.RegNullSet

end
