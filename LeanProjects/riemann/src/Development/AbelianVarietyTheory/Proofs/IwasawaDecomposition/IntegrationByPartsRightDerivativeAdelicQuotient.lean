import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotVolumeNeZeroNeTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.IntByParts

theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hm : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc _ _ _
  rw [← hm.setIntegral_preimage_emb (measurableEmbedding_mulRight a) Φ 𝓕]
  exact h.setIntegral_eq h' (f := fun g => Φ (g * a)) fun γ g => by
    change Φ ((γ : G) * g * a) = _
    rw [mul_assoc, hΦ _ γ.2]

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Φ Φ' : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hc' : Continuous Φ')
    {B B' : ℝ} (hB : ∀ g, ‖Φ g‖ ≤ B) (hB' : ∀ g, ‖Φ' g‖ ≤ B') {a : ℝ → G} (h0 : a 0 = 1)
    (hd : ∀ g t, HasDerivAt (fun s : ℝ => Φ (g * a s)) (Φ' (g * a t)) t) : ∫ g in 𝓕, Φ' g ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t g => Φ (g * a t)) (F' := fun t g => Φ' (g * a t)) (s := Set.univ) (bound := fun _ => B')
    Filter.univ_mem
    (.of_forall fun t => (hc.comp (continuous_mul_right _)).measurable.aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (continuous_mul_right _)).measurable.aestronglyMeasurable B
      (.of_forall fun g => hB _))
    (hc'.comp (continuous_mul_right _)).measurable.aestronglyMeasurable
    (.of_forall fun g t _ => hB' _) (integrable_const _) (.of_forall fun g t _ => hd g t)
  have h2 := key.2
  simp only [setIntegral_mul_right Γ μ h hΦ, h0, mul_one] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem mul_cont_bounded {φ F : GA D V → ℂ} (hφ : IsMod θ V φ) (hF : F ∈ Decay θ V) :
    Continuous (fun g => φ g * F g) ∧ ∃ B : ℝ, ∀ g, ‖φ g * F g‖ ≤ B := by
  obtain ⟨c1, N, C, hC⟩ := hφ.2.2 [] (by simp)
  obtain ⟨c2, hr⟩ := hF.2.2 [] (by simp)
  obtain ⟨B, hB⟩ := IsRapidDecay.mul_bounded (φ := F) (ψ := φ) hr hφ.2.1 hC
  exact ⟨Continuous.mul c1 c2, B, fun g => by rw [norm_mul]; exact hB g⟩

theorem integral_Rder_mul : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ X hX φ F hφ hF
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hq).2
  haveI := hq.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hq.1).1
  have int : ∀ {φ F : GA D V → ℂ}, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ := by
    intro φ F hφ hF
    obtain ⟨c, B, hB⟩ := mul_cont_bounded hφ hF
    exact Measure.integrableOn_of_bounded (M := B) hfin c.measurable.aestronglyMeasurable (.of_forall hB)
  refine ⟨int hφ hF, ?_⟩
  obtain ⟨c0, B0, hB0⟩ := mul_cont_bounded hφ hF
  obtain ⟨c1, B1, hB1⟩ := mul_cont_bounded (hφ.rder hX) hF
  obtain ⟨c2, B2, hB2⟩ := mul_cont_bounded hφ (Rder_mem_Decay hF hX)
  have key := setIntegral_deriv_eq_zero (GQ V) μ hq.2 hfin (Φ := fun g => φ g * F g)
    (Φ' := fun g => Rder θ V τ X φ g * F g + φ g * Rder θ V τ X F g)
    (fun γ hγ g => by simp only [hφ.2.1 γ hγ, hF.2.1 γ hγ]) c0 (c1.add c2) hB0
    (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g))) (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    fun g t => (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hφ.1 hX) g t).mul
      (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hF.1 hX) g t)
  rw [integral_add (int (hφ.rder hX) hF) (int hφ (Rder_mem_Decay hF hX))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.Mem.IntByParts

end
