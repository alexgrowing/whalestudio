import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteSupport
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.CuspL2

theorem exists_toLp_ext {G : Type} [MeasurableSpace G] (ν : Measure G) :
    ∃ E : (G → ℂ) →ₗ[ℂ] Lp ℂ 2 ν, ∀ φ, MemLp φ 2 ν → E φ =ᵐ[ν] φ := by
  classical
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {φ | MemLp φ 2 ν}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := by
        first
          | exact MemLp.zero
          | exact MemLp.zero'
          | exact zero_memLp
          | simp
      smul_mem' := fun c _ h => h.const_smul c }
  let f : S →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun φ => MemLp.toLp (φ : G → ℂ) φ.2
      map_add' := fun φ ψ => MemLp.toLp_add φ.2 ψ.2
      map_smul' := fun c φ => MemLp.toLp_const_smul c φ.2 }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend f
  refine ⟨E, fun φ hφ => ?_⟩
  have hval : E φ = f ⟨φ, hφ⟩ := LinearMap.congr_fun hE ⟨φ, hφ⟩
  rw [hval]
  exact MemLp.coeFn_toLp hφ

theorem inner_eq {G : Type} [MeasurableSpace G] {ν : Measure G} {f f' : Lp ℂ 2 ν} {φ φ' : G → ℂ}
    (h : f =ᵐ[ν] φ) (h' : f' =ᵐ[ν] φ') : ⟪f, f'⟫_ℂ = ∫ g, (starRingEnd ℂ) (φ g) * φ' g ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h, h'] with g hg hg'
  rw [hg, hg']
  first
    | (rw [RCLike.inner_apply]; try ring)
    | simp [mul_comm]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem bounded (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) {φ : GA D V → ℂ} (h : IsCuspGrow θ V φ) :
    ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B := by
  obtain ⟨ha, hs, hc, hg⟩ := h
  obtain ⟨-, -, hd⟩ := GlobalTheory.Size.rapidDec_of_cuspDecaySobolev hP hθ ha hs hg hc
  obtain ⟨C, hC⟩ := hd 0
  exact ⟨C, fun g => by simpa using hC g⟩

theorem conj_mul {G : Type} [TopologicalSpace G] {φ φ' : G → ℂ} (c : Continuous φ) (c' : Continuous φ')
    (b : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B) (b' : ∃ B : ℝ, ∀ g, ‖φ' g‖ ≤ B) :
    Continuous (fun g => (starRingEnd ℂ) (φ g) * φ' g) ∧ ∃ B : ℝ, ∀ g, ‖(starRingEnd ℂ) (φ g) * φ' g‖ ≤ B := by
  obtain ⟨B, hB⟩ := b
  obtain ⟨B', hB'⟩ := b'
  refine ⟨(Complex.continuous_conj.comp c).mul c', max B 0 * max B' 0, fun g => ?_⟩
  calc ‖(starRingEnd ℂ) (φ g) * φ' g‖ = ‖φ g‖ * ‖φ' g‖ := by simp [norm_mul]
    _ ≤ max B 0 * max B' 0 :=
      mul_le_mul ((hB g).trans (le_max_left _ _)) ((hB' g).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)

theorem exists_embedding_skew : GlobalTheory.Published.CuspDecaySobolev → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∃ E : (GA D V → ℂ) →ₗ[ℂ] Lp ℂ 2 (μ.restrict 𝓕), (∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) ∧ (E φ = 0 → φ = 0)) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ φ', IsCuspGrow θ V φ → IsCuspGrow θ V φ' → IsCuspGrow θ V (Rder θ V τ X φ) → IsCuspGrow θ V (Rder θ V τ X φ') → ⟪E (Rder θ V τ X φ), E φ'⟫_ℂ + ⟪E φ, E (Rder θ V τ X φ')⟫_ℂ = 0 := by
  intro hP D θ V μ 𝓕 hθ hμ h𝓕
  haveI := hμ
  obtain ⟨-, -, -, iB, iT, -, iC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := iB
  haveI := iT
  haveI := iC
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ).1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 (And.intro hμ h𝓕)).2
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hmem : ∀ φ, IsCuspGrow θ V φ → MemLp φ 2 (μ.restrict 𝓕) := by
    intro φ hφ
    obtain ⟨B, hB⟩ := bounded hP hθ hφ
    exact MemLp.of_bound hφ.1.cont.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hint : ∀ F : GA D V → ℂ, Continuous F → (∃ B : ℝ, ∀ g, ‖F g‖ ≤ B) → Integrable F (μ.restrict 𝓕) := by
    rintro F hF ⟨B, hB⟩
    exact memLp_one_iff_integrable.1 (MemLp.of_bound hF.aestronglyMeasurable B (Filter.Eventually.of_forall hB))
  obtain ⟨E, hE⟩ := exists_toLp_ext (μ.restrict 𝓕)
  refine ⟨E, fun φ hφ => ⟨hmem φ hφ, fun h0 => ?_⟩, ?_⟩
  · have h1 := hE φ (hmem φ hφ)
    rw [h0] at h1
    have hz : ⇑(0 : Lp ℂ 2 (μ.restrict 𝓕)) =ᵐ[μ.restrict 𝓕] (0 : GA D V → ℂ) := Lp.coeFn_zero ..
    have hae : ∀ᵐ g ∂(μ.restrict 𝓕), φ g = 0 := by
      filter_upwards [h1, hz] with g a b
      rw [← a, b]
      rfl
    have hopen : IsOpen {g | φ g ≠ 0} := isOpen_ne_fun hφ.1.cont continuous_const
    haveI : SMulInvariantMeasure (GQ V) (GA D V) μ := by
      first
        | exact inferInstance
        | exact ⟨fun γ s _ => measure_preimage_mul μ (γ : GA D V) s⟩
    open Pointwise in
    have hinv : ∀ γ : GQ V, γ • {g | φ g ≠ 0} = {g | φ g ≠ 0} := by
      intro γ
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      show φ ((γ⁻¹ : GQ V) * x) ≠ 0 ↔ φ x ≠ 0
      rw [hφ.1.left _ (γ⁻¹).2 x]
    have hnull : μ {g | φ g ≠ 0} = 0 := by
      refine h𝓕.measure_zero_of_invariant _ hinv ?_
      rw [← Measure.restrict_apply hopen.measurableSet]
      exact ae_iff.1 hae
    have hempty := (hopen.measure_eq_zero_iff μ).1 hnull
    funext g
    by_contra hne
    have hg : g ∈ {g | φ g ≠ 0} := hne
    rw [hempty] at hg
    exact hg
  · intro τ X hX φ φ' h1 h2 h3 h4
    rw [inner_eq (hE _ (hmem _ h3)) (hE _ (hmem _ h2)), inner_eq (hE _ (hmem _ h1)) (hE _ (hmem _ h4))]
    obtain ⟨c1, B1, b1⟩ := conj_mul h3.1.cont h2.1.cont (bounded hP hθ h3) (bounded hP hθ h2)
    obtain ⟨c2, B2, b2⟩ := conj_mul h1.1.cont h4.1.cont (bounded hP hθ h1) (bounded hP hθ h4)
    obtain ⟨c0, B0, b0⟩ := conj_mul h1.1.cont h2.1.cont (bounded hP hθ h1) (bounded hP hθ h2)
    rw [← integral_add (hint _ c1 ⟨B1, b1⟩) (hint _ c2 ⟨B2, b2⟩)]
    have key : ∀ ψ : GA D V → ℂ, ψ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V → ∀ g t,
        HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X s)) (Rder θ V τ X ψ (g * oneP θ V τ X t)) t := by
      intro ψ hψ g t
      have d0 : HasDerivAt (fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) 0 :=
        ((GlobalTheory.Mem.AutSpace.differentiable_oneP hψ hX (g * oneP θ V τ X t)) 0).hasDerivAt
      have d1 : HasDerivAt (fun s : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t)))
          (Rder θ V τ X ψ (g * oneP θ V τ X t)) t :=
        HasDerivAt.comp_sub_const (f := fun u : ℝ => ψ (g * oneP θ V τ X t * oneP θ V τ X u)) t t
          (by rw [sub_self]; exact d0)
      refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      show ψ (g * oneP θ V τ X s) = ψ (g * oneP θ V τ X t * oneP θ V τ X (s - t))
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, show t + (s - t) = s by ring]
    have hd : ∀ g t, HasDerivAt
        (fun s : ℝ => (starRingEnd ℂ) (φ (g * oneP θ V τ X s)) * φ' (g * oneP θ V τ X s))
        ((starRingEnd ℂ) (Rder θ V τ X φ (g * oneP θ V τ X t)) * φ' (g * oneP θ V τ X t) +
          (starRingEnd ℂ) (φ (g * oneP θ V τ X t)) * Rder θ V τ X φ' (g * oneP θ V τ X t)) t := by
      intro g t
      exact ((key φ h1.2.1 g t).star).mul (key φ' h2.2.1 g t)
    exact GlobalTheory.Mem.IntByParts.setIntegral_deriv_eq_zero (GQ V) μ h𝓕 hfin
      (Φ := fun g => (starRingEnd ℂ) (φ g) * φ' g)
      (Φ' := fun g => (starRingEnd ℂ) (Rder θ V τ X φ g) * φ' g + (starRingEnd ℂ) (φ g) * Rder θ V τ X φ' g)
      (fun γ hγ g => by
        show (starRingEnd ℂ) (φ (γ * g)) * φ' (γ * g) = (starRingEnd ℂ) (φ g) * φ' g
        rw [h1.1.left γ hγ g, h2.1.left γ hγ g])
      c0 (c1.add c2) b0
      (fun g => (norm_add_le _ _).trans (add_le_add (b1 g) (b2 g)))
      (GlobalTheory.Mem.Lift.oneP_zero hθ) hd

end GlobalTheory.Chain.CuspL2

end
