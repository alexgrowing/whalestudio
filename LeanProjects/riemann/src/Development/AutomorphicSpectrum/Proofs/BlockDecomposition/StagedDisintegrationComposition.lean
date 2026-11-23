import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationParameterContinuousStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.StageAbs

open Set Filter
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes (IsFibreFamily)

section Slice

variable {W V : Type} [TopologicalSpace W] [TopologicalSpace V] {ψ : W × V → ℝ}

theorem tsupport_slice (w : W) :
    tsupport (fun v => ψ (w, v)) ⊆ (fun v => (w, v)) ⁻¹' tsupport ψ :=
  closure_minimal (fun _ hv => subset_tsupport _ hv)
    ((isClosed_tsupport ψ).preimage (by fun_prop))

theorem slice_compact (hs : HasCompactSupport ψ) (w : W) :
    HasCompactSupport (fun v => ψ (w, v)) :=
  IsCompact.of_isClosed_subset (hs.isCompact.image continuous_snd) (isClosed_tsupport _)
    fun v hv => ⟨(w, v), tsupport_slice w hv, rfl⟩

end Slice

theorem lintegral_ofReal_fibre {W V X Y : Type} [TopologicalSpace W] [TopologicalSpace V]
    [MeasurableSpace V] [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {ν : Measure X}
    {f : V → Y} {ι : X → Y} {U : Set V} {fam : X → Measure V}
    (h : IsFibreFamily μ f ι U ν univ fam) {ψ : W × V → ℝ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) (hU : ∀ p ∈ tsupport ψ, p.2 ∈ U) (h0 : ∀ p, 0 ≤ ψ p) (w : W) (b : X) :
    ∫⁻ v, ENNReal.ofReal (ψ (w, v)) ∂(fam b) = ENNReal.ofReal (∫ v, ψ (w, v) ∂(fam b)) := by
  have hI := (h.2.2 (fun v => ψ (w, v)) (by fun_prop) (slice_compact hs w)
    (fun v hv => hU _ (tsupport_slice w hv))).1 b (mem_univ b)
  exact (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun v => h0 _)).symm

theorem param_integral {X A : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [FirstCountableTopology X] [TopologicalSpace A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] (α : Measure A) [IsLocallyFiniteMeasure α] {g : X × A → ℝ}
    (hc : Continuous g) (hs : HasCompactSupport g) :
    Continuous (fun x => ∫ a, g (x, a) ∂α) ∧ HasCompactSupport (fun x => ∫ a, g (x, a) ∂α) ∧
      tsupport (fun x => ∫ a, g (x, a) ∂α) ⊆ Prod.fst '' tsupport g := by
  have hK : IsCompact (Prod.snd '' tsupport g) := hs.isCompact.image continuous_snd
  have hF : IsCompact (Prod.fst '' tsupport g) := hs.isCompact.image continuous_fst
  have hz : ∀ p, p ∉ tsupport g → g p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport hp
  have e : (fun x => ∫ a, g (x, a) ∂α) = fun x => ∫ a in Prod.snd '' tsupport g, g (x, a) ∂α := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => hz _ fun hp => ha ?_).symm
    exact ⟨_, hp, rfl⟩
  have hsub : tsupport (fun x => ∫ a, g (x, a) ∂α) ⊆ Prod.fst '' tsupport g := by
    refine closure_minimal (fun x hx => ?_) hF.isClosed
    by_contra hn
    refine hx ?_
    have : ∀ a, g (x, a) = 0 := fun a => hz _ fun hp => hn ⟨_, hp, rfl⟩
    simp [this]
  refine ⟨?_, IsCompact.of_isClosed_subset hF (isClosed_tsupport _) hsub, hsub⟩
  rw [e]
  exact continuous_parametric_integral_of_continuous (f := fun x a => g (x, a))
    (by simpa [Function.uncurry_def] using hc) hK

theorem swap3 {A P H : Type} [MeasurableSpace A] [MeasurableSpace P] [MeasurableSpace H]
    (α : Measure A) (ρ : Measure P) (ν : Measure H) [SFinite α] [SFinite ρ] [SFinite ν]
    {h : A × P × H → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ a, ∫⁻ s, ∫⁻ Z, h (a, s, Z) ∂ν ∂ρ ∂α = ∫⁻ s, ∫⁻ Z, ∫⁻ a, h (a, s, Z) ∂α ∂ν ∂ρ := by
  have h0 : Measurable (fun p : (A × P) × H => h (p.1.1, p.1.2, p.2)) := hh.comp (by fun_prop)
  have h1 : Measurable (fun p : A × P => ∫⁻ Z, h (p.1, p.2, Z) ∂ν) :=
    h0.lintegral_prod_right'
  rw [lintegral_lintegral_swap (f := fun a s => ∫⁻ Z, h (a, s, Z) ∂ν)
    (by simpa [Function.uncurry_def] using h1.aemeasurable)]
  refine lintegral_congr fun s => ?_
  refine lintegral_lintegral_swap (f := fun a Z => h (a, s, Z)) ?_
  have h2 : Measurable (fun p : A × H => h (p.1, s, p.2)) := hh.comp (by fun_prop)
  simpa [Function.uncurry_def] using h2.aemeasurable

theorem lintegral_eq_setLIntegral {V : Type} [MeasurableSpace V] {μ : Measure V} {U : Set V}
    (hU : MeasurableSet U) {φ : V → ℝ≥0∞} (hφ : ∀ v, v ∉ U → φ v = 0) :
    ∫⁻ v, φ v ∂μ = ∫⁻ v in U, φ v ∂μ := by
  rw [← lintegral_indicator hU]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ U
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, hφ v hv]

theorem lintegral_mul_base' {D H Y : Type} [TopologicalSpace D] [MeasurableSpace D] [BorelSpace D]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] {δ : Measure D} {ν : Measure H}
    {f : D → Y} {ι : H → Y} {q : D → H} {U : Set D} {m : H → Measure D} (hUo : IsOpen U)
    (hq : Continuous q) (hι : Function.Injective ι) (hf : ∀ v, f v = ι (q v))
    (h : IsFibreFamily δ f ι U ν univ m) {φ : D → ℝ≥0∞} (hφ : Measurable φ)
    (h0 : ∀ v, v ∉ U → φ v = 0) {F : H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ Y, φ Y * F (q Y) ∂δ = ∫⁻ Z, F Z * ∫⁻ Y, φ Y ∂(m Z) ∂ν := by
  rw [lintegral_eq_setLIntegral hUo.measurableSet (fun v hv => by simp [h0 v hv]),
    h.2.1 (fun v => φ v * F (q v)) (hφ.mul (hF.comp hq.measurable))]
  refine lintegral_congr fun b => ?_
  have h1 : ∫⁻ Y, φ Y * F (q Y) ∂(m b) = ∫⁻ Y, F b * φ Y ∂(m b) := by
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily hι hf h b] with Y hY
    rw [hY.1, mul_comm]
  rw [h1, lintegral_const_mul _ hφ]

section Stages

variable {V₁ D H₁ H₃ A P Y₁ Y₃ : Type}
  [TopologicalSpace V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D]
  [MeasurableSpace D] [BorelSpace D]
  [TopologicalSpace H₁] [T2Space H₁] [LocallyCompactSpace H₁] [SecondCountableTopology H₁]
  [MeasurableSpace H₁] [BorelSpace H₁]
  [TopologicalSpace H₃] [T2Space H₃] [LocallyCompactSpace H₃] [SecondCountableTopology H₃]
  [MeasurableSpace H₃] [BorelSpace H₃]
  [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  [MeasurableSpace A] [BorelSpace A]
  [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] [SecondCountableTopology P]
  [MeasurableSpace P] [BorelSpace P]

theorem stage_three {δ : Measure D} {ν₃ : Measure H₃} {f₃ : D → Y₃} {ι₃ : H₃ → Y₃} {q₃ : D → H₃}
    {U₁ : Set V₁} {U₃ : Set D} {m₃ : H₃ → Measure D} (hU₃ : IsOpen U₃) (hq₃ : Continuous q₃)
    (hι₃ : Function.Injective ι₃) (hf₃ : ∀ v, f₃ v = ι₃ (q₃ v))
    (hm₃ : IsFibreFamily δ f₃ ι₃ U₃ ν₃ univ m₃) {ψ : V₁ × A × P × D → ℝ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) (hψt : ∀ p ∈ tsupport ψ, p.1 ∈ U₁ ∧ p.2.2.2 ∈ U₃)
    (hψ0 : ∀ p, 0 ≤ ψ p) :
    ∃ θ : (V₁ × A × P) × H₃ → ℝ, Continuous θ ∧ HasCompactSupport θ ∧
      (∀ z ∈ tsupport θ, z.1.1 ∈ U₁) ∧ (∀ z, 0 ≤ θ z) ∧
      ∀ x a s Z, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) ∂(m₃ Z) =
        ENNReal.ofReal (θ ((x, a, s), Z)) := by
  let e : ((V₁ × A × P) × D) ≃ₜ (V₁ × A × P × D) :=
    (Homeomorph.prodAssoc _ _ _).trans ((Homeomorph.refl _).prodCongr (Homeomorph.prodAssoc _ _ _))
  have hc : Continuous (ψ ∘ e) := hψc.comp e.continuous
  have hs : HasCompactSupport (ψ ∘ e) := hψs.comp_homeomorph e
  have ht : ∀ p ∈ tsupport (ψ ∘ e), e p ∈ tsupport ψ := fun p hp => by
    rwa [tsupport_comp_eq_preimage] at hp
  have hU : ∀ p ∈ tsupport (ψ ∘ e), p.2 ∈ U₃ := fun p hp => (hψt _ (ht p hp)).2
  obtain ⟨c1, c2, c3⟩ := GlobalTheory.T.disintegration_parameter_continuous D H₃ Y₃ (V₁ × A × P) δ ν₃ f₃ ι₃ q₃ U₃ m₃ hU₃ hq₃ hι₃ hf₃ hm₃
    (ψ ∘ e) hc hs hU
  refine ⟨_, c1, c2, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨v, hv, -⟩ := c3 z hz
    exact (hψt _ (ht _ hv)).1
  · intro z
    exact integral_nonneg fun v => hψ0 _
  · intro x a s Z
    exact lintegral_ofReal_fibre hm₃ hc hs hU (fun p => hψ0 _) (x, a, s) Z

theorem stage_two (α : Measure A) [IsLocallyFiniteMeasure α] [AddCommGroup H₃]
    [IsTopologicalAddGroup H₃] {q₁ : V₁ → H₁} (hq₁ : Continuous q₁) {Q : H₁ × P × A → H₃}
    (hQ : Continuous Q) {U₁ : Set V₁} {θ : (V₁ × A × P) × H₃ → ℝ} (hθc : Continuous θ)
    (hθs : HasCompactSupport θ) (hθt : ∀ z ∈ tsupport θ, z.1.1 ∈ U₁) (hθ0 : ∀ z, 0 ≤ θ z) :
    ∃ ξ : V₁ × P × H₃ → ℝ, Continuous ξ ∧ HasCompactSupport ξ ∧ (∀ y ∈ tsupport ξ, y.1 ∈ U₁) ∧
      (∀ y, 0 ≤ ξ y) ∧
      ∀ x s Z, ∫⁻ a, ENNReal.ofReal (θ ((x, a, s), Z - Q (q₁ x, s, a))) ∂α =
        ENNReal.ofReal (ξ (x, s, Z)) := by
  let E : ((V₁ × P × H₃) × A) ≃ₜ ((V₁ × A × P) × H₃) :=
    { toFun := fun p => ((p.1.1, p.2, p.1.2.1), p.1.2.2 - Q (q₁ p.1.1, p.1.2.1, p.2))
      invFun := fun r => ((r.1.1, r.1.2.2, r.2 + Q (q₁ r.1.1, r.1.2.2, r.1.2.1)), r.1.2.1)
      left_inv := fun p => by simp
      right_inv := fun r => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : Continuous (θ ∘ E) := hθc.comp E.continuous
  have hs : HasCompactSupport (θ ∘ E) := hθs.comp_homeomorph E
  obtain ⟨c1, c2, c3⟩ := param_integral α hc hs
  refine ⟨_, c1, c2, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := c3 hy
    rw [tsupport_comp_eq_preimage] at hp
    exact hθt _ hp
  · intro y
    exact integral_nonneg fun a => hθ0 _
  · intro x s Z
    have hI : Integrable (fun a => (θ ∘ E) ((x, s, Z), a)) α :=
      (hc.comp (by fun_prop)).integrable_of_hasCompactSupport (slice_compact hs _)
    exact (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun a => hθ0 _)).symm

theorem stage_one {μ₁ : Measure V₁} {ν₁ : Measure H₁} {f₁ : V₁ → Y₁} {ι₁ : H₁ → Y₁} {q₁ : V₁ → H₁}
    {U₁ : Set V₁} {m₁ : H₁ → Measure V₁} (hU₁ : IsOpen U₁) (hq₁ : Continuous q₁)
    (hι₁ : Function.Injective ι₁) (hf₁ : ∀ v, f₁ v = ι₁ (q₁ v))
    (hm₁ : IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ univ m₁) {ξ : V₁ × P × H₃ → ℝ} (hξc : Continuous ξ)
    (hξs : HasCompactSupport ξ) (hξt : ∀ y ∈ tsupport ξ, y.1 ∈ U₁) (hξ0 : ∀ y, 0 ≤ ξ y) :
    Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1)) := by
  let e : ((P × H₃) × V₁) ≃ₜ (V₁ × P × H₃) := Homeomorph.prodComm _ _
  have hc : Continuous (ξ ∘ e) := hξc.comp e.continuous
  have hs : HasCompactSupport (ξ ∘ e) := hξs.comp_homeomorph e
  have hU : ∀ p ∈ tsupport (ξ ∘ e), p.2 ∈ U₁ := fun p hp => by
    rw [tsupport_comp_eq_preimage] at hp
    exact hξt _ hp
  obtain ⟨c1, -, -⟩ := GlobalTheory.T.disintegration_parameter_continuous V₁ H₁ Y₁ (P × H₃) μ₁ ν₁ f₁ ι₁ q₁ U₁ m₁ hU₁ hq₁ hι₁ hf₁ hm₁
    (ξ ∘ e) hc hs hU
  have e1 : (fun z : H₁ × P × H₃ => ∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1)) =
      fun z => ENNReal.ofReal (∫ v, (ξ ∘ e) (z.2, v) ∂(m₁ z.1)) := by
    funext z
    exact lintegral_ofReal_fibre hm₁ hc hs hU (fun p => hξ0 _) z.2 z.1
  rw [e1]
  exact ENNReal.continuous_ofReal.comp (c1.comp (continuous_snd.prodMk continuous_fst))

theorem disint_inner [AddCommGroup H₃] [IsTopologicalAddGroup H₃] {δ : Measure D}
    {ν₃ : Measure H₃} (α : Measure A) (ρ : Measure P) [ν₃.IsAddHaarMeasure]
    [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure ρ]
    {f₃ : D → Y₃} {ι₃ : H₃ → Y₃} {q₃ : D → H₃} {U₃ : Set D} {m₃ : H₃ → Measure D}
    (hU₃ : IsOpen U₃) (hq₃ : Continuous q₃) (hι₃ : Function.Injective ι₃)
    (hf₃ : ∀ v, f₃ v = ι₃ (q₃ v)) (hm₃ : IsFibreFamily δ f₃ ι₃ U₃ ν₃ univ m₃)
    {q₁ : V₁ → H₁} (hq₁ : Continuous q₁) {Q : H₁ × P × A → H₃} (hQ : Continuous Q)
    {ψ : V₁ × A × P × D → ℝ} (hψc : Continuous ψ) (hψt : ∀ p, p.2.2.2 ∉ U₃ → ψ p = 0)
    {θ : (V₁ × A × P) × H₃ → ℝ} (hθc : Continuous θ)
    (hθ : ∀ x a s Z, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) ∂(m₃ Z) =
      ENNReal.ofReal (θ ((x, a, s), Z)))
    {ξ : V₁ × P × H₃ → ℝ}
    (hξ : ∀ x s Z, ∫⁻ a, ENNReal.ofReal (θ ((x, a, s), Z - Q (q₁ x, s, a))) ∂α =
      ENNReal.ofReal (ξ (x, s, Z)))
    {f : H₁ × P × H₃ → ℝ≥0∞} (hf : Measurable f) (x : V₁) :
    ∫⁻ a, ∫⁻ s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) * f (q₁ x, s, q₃ Y + Q (q₁ x, s, a))
        ∂δ ∂ρ ∂α =
      ∫⁻ s, ∫⁻ Z, f (q₁ x, s, Z) * ENNReal.ofReal (ξ (x, s, Z)) ∂ν₃ ∂ρ := by
  have hin : ∀ a s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) * f (q₁ x, s, q₃ Y + Q (q₁ x, s, a)) ∂δ =
      ∫⁻ Z, f (q₁ x, s, Z) * ENNReal.ofReal (θ ((x, a, s), Z - Q (q₁ x, s, a))) ∂ν₃ := by
    intro a s
    have hφ : Measurable fun Y => ENNReal.ofReal (ψ (x, a, s, Y)) :=
      ENNReal.measurable_ofReal.comp (hψc.comp (by fun_prop)).measurable
    have hF : Measurable fun Z => f (q₁ x, s, Z + Q (q₁ x, s, a)) :=
      hf.comp (by fun_prop)
    rw [lintegral_mul_base' hU₃ hq₃ hι₃ hf₃ hm₃ hφ
      (fun v hv => by rw [hψt (x, a, s, v) hv]; simp) hF]
    rw [← lintegral_add_right_eq_self
      (fun Z => f (q₁ x, s, Z) * ENNReal.ofReal (θ ((x, a, s), Z - Q (q₁ x, s, a))))
      (Q (q₁ x, s, a))]
    refine lintegral_congr fun Z => ?_
    rw [hθ, add_sub_cancel_right]
  simp only [hin]
  have hθm : Measurable fun p : A × P × H₃ =>
      ENNReal.ofReal (θ ((x, p.1, p.2.1), p.2.2 - Q (q₁ x, p.2.1, p.1))) :=
    ENNReal.measurable_ofReal.comp (hθc.comp (by fun_prop)).measurable
  have hg : Measurable fun p : A × P × H₃ => f (q₁ x, p.2.1, p.2.2) *
      ENNReal.ofReal (θ ((x, p.1, p.2.1), p.2.2 - Q (q₁ x, p.2.1, p.1))) :=
    (hf.comp (by fun_prop)).mul hθm
  rw [swap3 α ρ ν₃ hg]
  refine lintegral_congr fun s => lintegral_congr fun Z => ?_
  have hθa : Measurable fun a => ENNReal.ofReal (θ ((x, a, s), Z - Q (q₁ x, s, a))) :=
    hθm.comp (by fun_prop : Measurable fun a : A => (a, s, Z))
  dsimp only
  rw [lintegral_const_mul _ hθa, hξ]

theorem disint_base [AddCommGroup H₃] {μ₁ : Measure V₁} {ν₁ : Measure H₁} {ν₃ : Measure H₃}
    (ρ : Measure P) [IsLocallyFiniteMeasure ν₁] [IsLocallyFiniteMeasure ν₃]
    [IsLocallyFiniteMeasure ρ] {f₁ : V₁ → Y₁} {ι₁ : H₁ → Y₁} {q₁ : V₁ → H₁}
    {U₁ : Set V₁} {m₁ : H₁ → Measure V₁} (hU₁ : IsOpen U₁) (hq₁ : Continuous q₁)
    (hι₁ : Function.Injective ι₁) (hf₁ : ∀ v, f₁ v = ι₁ (q₁ v))
    (hm₁ : IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ univ m₁) {ξ : V₁ × P × H₃ → ℝ} (hξc : Continuous ξ)
    (hξt : ∀ y, y.1 ∉ U₁ → ξ y = 0)
    (hL : Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1)))
    {f : H₁ × P × H₃ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, ∫⁻ s, ∫⁻ Z, f (q₁ x, s, Z) * ENNReal.ofReal (ξ (x, s, Z)) ∂ν₃ ∂ρ ∂μ₁ =
      ∫⁻ z, f z * (∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1)) ∂(ν₁.prod (ρ.prod ν₃)) := by
  have hξm : Measurable fun p : V₁ × P × H₃ => ENNReal.ofReal (ξ p) :=
    ENNReal.measurable_ofReal.comp hξc.measurable
  have hg : Measurable fun p : V₁ × P × H₃ => f (q₁ p.1, p.2.1, p.2.2) * ENNReal.ofReal (ξ p) :=
    (hf.comp (by fun_prop)).mul hξm
  have hΦ1 : Measurable fun p : V₁ × P =>
      ∫⁻ Z, f (q₁ p.1, p.2, Z) * ENNReal.ofReal (ξ (p.1, p.2, Z)) ∂ν₃ :=
    (hg.comp (by fun_prop : Measurable fun p : (V₁ × P) × H₃ => (p.1.1, p.1.2, p.2))).lintegral_prod_right'
  have hΦ : Measurable fun x => ∫⁻ s, ∫⁻ Z, f (q₁ x, s, Z) * ENNReal.ofReal (ξ (x, s, Z)) ∂ν₃ ∂ρ :=
    hΦ1.lintegral_prod_right'
  rw [lintegral_eq_setLIntegral hU₁.measurableSet (fun v hv => by
    simp [hξt (v, _) hv]), hm₁.2.1 _ hΦ]
  have hfm : Measurable fun z : H₁ × P × H₃ =>
      f z * ∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1) := hf.mul hL.measurable
  rw [lintegral_prod _ hfm.aemeasurable]
  refine lintegral_congr fun t => ?_
  haveI := GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_fib hm₁ hU₁ t
  have hh : Measurable fun p : V₁ × P × H₃ => f (t, p.2.1, p.2.2) * ENNReal.ofReal (ξ p) :=
    (hf.comp (by fun_prop)).mul hξm
  have e1 : ∫⁻ x, ∫⁻ s, ∫⁻ Z, f (q₁ x, s, Z) * ENNReal.ofReal (ξ (x, s, Z)) ∂ν₃ ∂ρ ∂(m₁ t) =
      ∫⁻ x, ∫⁻ s, ∫⁻ Z, f (t, s, Z) * ENNReal.ofReal (ξ (x, s, Z)) ∂ν₃ ∂ρ ∂(m₁ t) := by
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily hι₁ hf₁ hm₁ t] with x hx
    rw [hx.1]
  rw [e1, swap3 (m₁ t) ρ ν₃ hh]
  have hfm2 : Measurable fun p : P × H₃ =>
      f (t, p) * ∫⁻ x, ENNReal.ofReal (ξ (x, p.1, p.2)) ∂(m₁ t) :=
    hfm.comp (by fun_prop : Measurable fun p : P × H₃ => (t, p))
  rw [lintegral_prod _ hfm2.aemeasurable]
  refine lintegral_congr fun s => lintegral_congr fun Z => ?_
  have hxm : Measurable fun x => ENNReal.ofReal (ξ (x, s, Z)) :=
    hξm.comp (by fun_prop : Measurable fun x : V₁ => (x, s, Z))
  dsimp only
  rw [lintegral_const_mul _ hxm]

theorem stages_compose_disintegration [AddCommGroup H₃] [IsTopologicalAddGroup H₃] (μ₁ : Measure V₁) (δ : Measure D)
    (ν₁ : Measure H₁) (ν₃ : Measure H₃) (α : Measure A) (ρ : Measure P)
    [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure δ] [IsLocallyFiniteMeasure ν₁]
    [ν₃.IsAddHaarMeasure] [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure ρ]
    (f₁ : V₁ → Y₁) (ι₁ : H₁ → Y₁) (q₁ : V₁ → H₁) (U₁ : Set V₁) (m₁ : H₁ → Measure V₁)
    (f₃ : D → Y₃) (ι₃ : H₃ → Y₃) (q₃ : D → H₃) (U₃ : Set D) (m₃ : H₃ → Measure D)
    (Q : H₁ × P × A → H₃) (hU₁ : IsOpen U₁) (hU₃ : IsOpen U₃) (hq₁ : Continuous q₁)
    (hq₃ : Continuous q₃) (hι₁ : Function.Injective ι₁) (hι₃ : Function.Injective ι₃)
    (hf₁ : ∀ v, f₁ v = ι₁ (q₁ v)) (hf₃ : ∀ v, f₃ v = ι₃ (q₃ v))
    (hm₁ : IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ Set.univ m₁)
    (hm₃ : IsFibreFamily δ f₃ ι₃ U₃ ν₃ Set.univ m₃) (hQ : Continuous Q)
    (ψ : V₁ × A × P × D → ℝ) (hψc : Continuous ψ) (hψs : HasCompactSupport ψ)
    (hψt : ∀ p ∈ tsupport ψ, p.1 ∈ U₁ ∧ p.2.2.2 ∈ U₃) (hψ0 : ∀ p, 0 ≤ ψ p) :
    Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
      ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∧
    ∀ f : H₁ × P × H₃ → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) *
        f (q₁ x, s, q₃ Y + Q (q₁ x, s, a)) ∂δ ∂ρ ∂α ∂μ₁ =
      ∫⁻ z, f z * (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
        ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∂(ν₁.prod (ρ.prod ν₃)) := by
  obtain ⟨θ, hθc, hθs, hθt, hθ0, hθ⟩ :=
    stage_three (U₁ := U₁) hU₃ hq₃ hι₃ hf₃ hm₃ hψc hψs hψt hψ0
  obtain ⟨ξ, hξc, hξs, hξt, hξ0, hξ⟩ := stage_two α hq₁ hQ hθc hθs hθt hθ0
  have hL := stage_one hU₁ hq₁ hι₁ hf₁ hm₁ hξc hξs hξt hξ0
  have key : ∀ z : H₁ × P × H₃, ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y))
      ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1) =
      ∫⁻ x, ENNReal.ofReal (ξ (x, z.2.1, z.2.2)) ∂(m₁ z.1) := by
    intro z
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.CompanionTheory.SW.FibreUniq.ae_eq_of_isFibreFamily hι₁ hf₁ hm₁ z.1] with x hx
    rw [← hξ x]
    refine lintegral_congr fun a => ?_
    rw [hθ, hx.1]
  have hψz : ∀ p, p.2.2.2 ∉ U₃ → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun ht => hp (hψt p ht).2
  have hξz : ∀ y, y.1 ∉ U₁ → ξ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun ht => hy (hξt y ht)
  refine ⟨by rw [funext key]; exact hL, fun f hf => ?_⟩
  simp only [key]
  rw [← disint_base ρ hU₁ hq₁ hι₁ hf₁ hm₁ hξc hξz hL hf]
  refine lintegral_congr fun x => ?_
  exact disint_inner α ρ hU₃ hq₃ hι₃ hf₃ hm₃ hq₁ hQ hψc hψz hθc hθ hξ hf x

end Stages

theorem stages_abstract : ∀ (V₁ D H₁ H₃ A P Y₁ Y₃ : Type) [TopologicalSpace V₁] [T2Space V₁] [LocallyCompactSpace V₁] [SecondCountableTopology V₁] [MeasurableSpace V₁] [BorelSpace V₁] [TopologicalSpace D] [T2Space D] [LocallyCompactSpace D] [SecondCountableTopology D] [MeasurableSpace D] [BorelSpace D] [TopologicalSpace H₁] [T2Space H₁] [LocallyCompactSpace H₁] [SecondCountableTopology H₁] [MeasurableSpace H₁] [BorelSpace H₁] [TopologicalSpace H₃] [T2Space H₃] [LocallyCompactSpace H₃] [SecondCountableTopology H₃] [MeasurableSpace H₃] [BorelSpace H₃] [TopologicalSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P] [AddCommGroup H₃] [IsTopologicalAddGroup H₃] (μ₁ : Measure V₁) (δ : Measure D) (ν₁ : Measure H₁) (ν₃ : Measure H₃) (α : Measure A) (ρ : Measure P) [IsLocallyFiniteMeasure μ₁] [IsLocallyFiniteMeasure δ] [IsLocallyFiniteMeasure ν₁] [ν₃.IsAddHaarMeasure] [IsLocallyFiniteMeasure α] [IsLocallyFiniteMeasure ρ] (f₁ : V₁ → Y₁) (ι₁ : H₁ → Y₁) (q₁ : V₁ → H₁) (U₁ : Set V₁) (m₁ : H₁ → Measure V₁) (f₃ : D → Y₃) (ι₃ : H₃ → Y₃) (q₃ : D → H₃) (U₃ : Set D) (m₃ : H₃ → Measure D) (Q : H₁ × P × A → H₃), IsOpen U₁ → IsOpen U₃ → Continuous q₁ → Continuous q₃ → Function.Injective ι₁ → Function.Injective ι₃ → (∀ v, f₁ v = ι₁ (q₁ v)) → (∀ v, f₃ v = ι₃ (q₃ v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ₁ f₁ ι₁ U₁ ν₁ Set.univ m₁ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily δ f₃ ι₃ U₃ ν₃ Set.univ m₃ → Continuous Q → ∀ ψ : V₁ × A × P × D → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.1 ∈ U₁ ∧ p.2.2.2 ∈ U₃) → (∀ p, 0 ≤ ψ p) → Continuous (fun z : H₁ × P × H₃ => ∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∧ ∀ f : H₁ × P × H₃ → ℝ≥0∞, Measurable f → ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, s, Y)) * f (q₁ x, s, q₃ Y + Q (q₁ x, s, a)) ∂δ ∂ρ ∂α ∂μ₁ = ∫⁻ z, f z * (∫⁻ x, ∫⁻ a, ∫⁻ Y, ENNReal.ofReal (ψ (x, a, z.2.1, Y)) ∂(m₃ (z.2.2 - Q (z.1, z.2.1, a))) ∂α ∂(m₁ z.1)) ∂(ν₁.prod (ρ.prod ν₃)) :=
  fun V₁ D H₁ H₃ A P Y₁ Y₃ => @stages_compose_disintegration V₁ D H₁ H₃ A P Y₁ Y₃

end GlobalTheory.CompanionTheory.WeilSiegel.StageAbs
