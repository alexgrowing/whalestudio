import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeightLocallyBounded

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem IsKerSys.mul_decay_le {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {F : GA D V → ℂ} (hF : IsRapidDecay θ V F) :
    ∃ N : ℕ, ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ‖κ f g h * F g‖ ≤ C * (height θ W h : ℝ) ^ N := by
  obtain ⟨N, hN⟩ := hκ.growth
  obtain ⟨C', hC'⟩ := hF N
  refine ⟨N, fun f => ?_⟩
  obtain ⟨C, hC⟩ := hN f
  refine ⟨|C| * 2 ^ N * |C'|, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖κ f g h‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N := by
    have := hκ.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [← this]
    exact (hC _ _).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (NNReal.coe_nonneg _)) N)
      (by positivity) (abs_nonneg _))
  calc ‖κ f g h * F g‖ = ‖κ f g h‖ * ‖F g‖ := norm_mul _ _
    _ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N * ‖F g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖F g‖ * (quotHeight θ V g : ℝ) ^ N) * (height θ W h : ℝ) ^ N := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ |C| * 2 ^ N * |C'| * (height θ W h : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hC' g).trans (le_abs_self _)) (by positivity))
          (by positivity)

theorem lift_conv_cont_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  intro D θ hθ V W M _ _ κ hκ μ 𝓕 hQ F hF
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have : SecondCountableTopology (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.1
  have : IsTopologicalGroup (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.2.2.2.1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hQ).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨hc, hd⟩ : Continuous F ∧ IsRapidDecay θ V F := hF.2.2 [] (by simp)
  obtain ⟨N, hN⟩ := hκ.mul_decay_le hd
  have hm : ∀ f h, AEStronglyMeasurable (fun g => κ f g h * F g) (μ.restrict 𝓕) := fun f h =>
    (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable
  have hint : ∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ := fun f h => by
    obtain ⟨C, -, hC⟩ := hN f
    exact Measure.integrableOn_of_bounded hfin
      (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable (.of_forall fun g => hC g h)
  have hloc : ∀ f h₀, ∃ B : ℝ, ∀ᶠ h in 𝓝 h₀, ∀ g, ‖κ f g h * F g‖ ≤ B := fun f h₀ => by
    obtain ⟨C, h0, hC⟩ := hN f
    obtain ⟨B, hB⟩ := GlobalTheory.Mem.LiftHeight.height_locally_bounded D θ hθ W h₀
    exact ⟨C * B ^ N, hB.mono fun h hh g => (hC g h).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh N) h0)⟩
  refine ⟨hint, fun f => continuous_iff_continuousAt.2 fun h₀ => ?_, ⟨N, fun f => ?_⟩, fun τ X hX f f' hder h => ?_⟩
  · obtain ⟨B, hB⟩ := hloc f h₀
    exact continuousAt_of_dominated (bound := fun _ => B) (.of_forall (hm f)) (hB.mono fun h hh => .of_forall hh)
      (integrable_const B) (.of_forall fun g =>
        (((hκ.cont f).comp (Continuous.prodMk_right g)).mul continuous_const).continuousAt)
  · obtain ⟨C, -, hC⟩ := hN f
    refine ⟨C * (μ.restrict 𝓕).real Set.univ, fun h => ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall fun g => hC g h)).trans_eq ?_
    ring
  · obtain ⟨B, hB⟩ := hloc f' h
    have hco : Filter.Tendsto (fun t : ℝ => h * oneP θ W τ X t) (𝓝 0) (𝓝 h) := by
      have := (continuous_const (y := h).mul (continuous_oneP hθ hX)).tendsto 0
      rw [Pi.mul_apply, oneP_zero hθ, mul_one] at this
      exact this
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
      (F := fun t g => κ f g (h * oneP θ W τ X t) * F g) (F' := fun t g => κ f' g (h * oneP θ W τ X t) * F g)
      (bound := fun _ => B) (hco.eventually hB) (.of_forall fun t => hm f _) (hint f _) (hm f' _)
      (.of_forall fun g t ht => ht g) (integrable_const B)
      (.of_forall fun g t _ => (hasDerivAt_oneP hθ hX (φ := κ f g) (φ' := κ f' g) (hder g) h t).mul_const (F g))).2
    simpa only [oneP_zero hθ, mul_one] using this

end GlobalTheory.Mem.Lift

end
