import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CuspCont

open Metric

theorem eq_zero_of_locally_holo (g : ℂ → ℂ) (s₀ : ℂ) (R₀ : ℝ)
    (hloc : ∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (G : ℂ → ℂ), 0 < r ∧ (s₁ = s₀ → k = 0) ∧
      DifferentiableOn ℂ G (ball s₁ r) ∧ ∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → G s = (s - s₁) ^ k * g s)
    (hvan : ∀ s : ℂ, R₀ < s.re → g s = 0) : g s₀ = 0 := by
  have hmero : MeromorphicOn g Set.univ := by
    intro s₁ _
    obtain ⟨k, r, G, hr, -, hG, hGg⟩ := hloc s₁
    refine ⟨k + 1, ?_⟩
    have hGa : AnalyticAt ℂ G s₁ := hG.analyticAt (ball_mem_nhds s₁ hr)
    have hA : AnalyticAt ℂ (fun z => (z - s₁) * G z) s₁ := (analyticAt_id.sub analyticAt_const).mul hGa
    refine hA.congr ?_
    filter_upwards [ball_mem_nhds s₁ hr] with z hz
    by_cases hzs : z = s₁
    · subst hzs; simp
    · rw [hGg z hz (Or.inl hzs), smul_eq_mul]; ring
  have hcl := hmero.isClopen_setOfPred_meromorphicOrderAt_eq_top
  haveI : PreconnectedSpace (Set.univ : Set ℂ) := Subtype.preconnectedSpace isPreconnected_univ
  have hne : (⟨((R₀ + 1 : ℝ) : ℂ), trivial⟩ : (Set.univ : Set ℂ)) ∈
      {u : (Set.univ : Set ℂ) | meromorphicOrderAt g u = ⊤} := by
    show meromorphicOrderAt g ((R₀ + 1 : ℝ) : ℂ) = ⊤
    rw [meromorphicOrderAt_eq_top_iff]
    have hopen : IsOpen {s : ℂ | R₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | R₀ < s.re} ∈ 𝓝 ((R₀ + 1 : ℝ) : ℂ) := hopen.mem_nhds (by simp)
    filter_upwards [nhdsWithin_le_nhds hmem] with s hs using hvan s hs
  have huniv := (isClopen_iff.1 hcl).resolve_left (Set.nonempty_iff_ne_empty.1 ⟨_, hne⟩)
  have h0 : meromorphicOrderAt g s₀ = ⊤ := by
    have hm : (⟨s₀, trivial⟩ : (Set.univ : Set ℂ)) ∈ {u : (Set.univ : Set ℂ) | meromorphicOrderAt g u = ⊤} := by
      rw [huniv]; trivial
    exact hm
  rw [meromorphicOrderAt_eq_top_iff] at h0
  obtain ⟨k, r, G, hr, hk, hG, hGg⟩ := hloc s₀
  have hk0 := hk rfl
  subst hk0
  have hGc : ContinuousAt G s₀ := (hG.differentiableAt (ball_mem_nhds s₀ hr)).continuousAt
  have hGs : ∀ s ∈ ball s₀ r, G s = g s := fun s hs => by simpa using hGg s hs (Or.inr rfl)
  have ht : Tendsto G (𝓝[≠] s₀) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [h0, nhdsWithin_le_nhds (ball_mem_nhds s₀ hr)] with s hs hb
    rw [hGs s hb, hs]
  have := tendsto_nhds_unique (hGc.tendsto.mono_left nhdsWithin_le_nhds) ht
  rw [← hGs s₀ (mem_ball_self hr), this]

theorem differentiableOn_integral_integral {X Y : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : Measure X) [IsFiniteMeasure ν] (μ : Measure Y) (φ : X → Y) (hφ : Continuous φ) (f : Y → ℂ) (hf : Continuous f)
    (Hf : ℂ → Y → Y → ℂ) {U : Set ℂ} (hU : IsOpen U) (hdiff : ∀ a b, DifferentiableOn ℂ (Hf · a b) U)
    (hcont : ∀ s ∈ U, Continuous fun p : Y × Y => Hf s p.1 p.2) (B : Y → ℝ) (hB : Integrable B μ)
    (hnorm : ∀ s ∈ U, ∀ x y, ‖f y * Hf s (φ x) y‖ ≤ B y) :
    DifferentiableOn ℂ (fun s => ∫ x, ∫ y, f y * Hf s (φ x) y ∂μ ∂ν) U := by
  have hc2 : ∀ s ∈ U, Continuous fun p : X × Y => f p.2 * Hf s (φ p.1) p.2 := fun s hs =>
    (hf.comp continuous_snd).mul ((hcont s hs).comp ((hφ.comp continuous_fst).prodMk continuous_snd))
  have hc3 : ∀ s ∈ U, ∀ x : X, Continuous fun y : Y => f y * Hf s (φ x) y :=
    fun s hs x => (hc2 s hs).comp (continuous_const.prodMk continuous_id : Continuous fun y : Y => (x, y))
  have hc4 : ∀ s ∈ U, ∀ y : Y, Continuous fun x : X => f y * Hf s (φ x) y :=
    fun s hs y => (hc2 s hs).comp (continuous_id.prodMk continuous_const : Continuous fun x : X => (x, y))
  have hinD : ∀ x : X, DifferentiableOn ℂ (fun s => ∫ y, f y * Hf s (φ x) y ∂μ) U := fun x =>
    (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ)
      (F := fun y s => f y * Hf s (φ x) y) hU
      (fun s hs => (hc3 s hs x).aestronglyMeasurable)
      (Eventually.of_forall fun y => (hdiff (φ x) y).const_mul (f y))
      (fun z hz => ⟨U, hU.mem_nhds hz, B, hB, Eventually.of_forall fun y s hs => hnorm s hs x y⟩)).1
  have hinC : ∀ s ∈ U, Continuous fun x : X => ∫ y, f y * Hf s (φ x) y ∂μ := fun s hs =>
    continuous_of_dominated (bound := B) (fun x => (hc3 s hs x).aestronglyMeasurable)
      (fun x => Eventually.of_forall fun y => hnorm s hs x y) hB (Eventually.of_forall fun y => hc4 s hs y)
  exact (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := ν)
    (F := fun x s => ∫ y, f y * Hf s (φ x) y ∂μ) hU
    (fun s hs => (hinC s hs).aestronglyMeasurable)
    (Eventually.of_forall hinD)
    (fun z hz => ⟨U, hU.mem_nhds hz, fun _ => ∫ y, B y ∂μ, integrable_const _,
      Eventually.of_forall fun x s hs =>
        norm_integral_le_of_norm_le hB (Eventually.of_forall fun y => hnorm s hs x y)⟩)).1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measUA in
local instance borelUAc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem isCT_integral_of_regFam : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d d₁ : ℕ}
    (W : Spc F E d) (H' : Plane E d d₁) (μ : Measure (UA σ W.J)), μ.IsHaarMeasure →
    ∀ (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (Ez : ℂ → UA σ W.J → UA σ W.J → ℂ) (s₀ : ℂ) (R₀ : ℝ), Continuous f →
      (∀ N : ℕ, IntegrableOn (fun h => ‖f h‖ * (qht h : ℝ) ^ N) 𝓕 μ) →
      (∀ h, ∃ C : ℝ, ∀ u ∈ unip σ W H', (qht (u * h) : ℝ) ≤ C) →
      GlobalTheory.CuspDbl.IsRegFam (fun h : UA σ W.J => (qht h : ℝ)) s₀ Ez →
      (∀ s : ℂ, R₀ < s.re → IsCT H' (fun h => ∫ h' in 𝓕, f h' * Ez s h h' ∂μ) 0) →
      IsCT H' (fun h => ∫ h' in 𝓕, f h' * Ez s₀ h h' ∂μ) 0 := by
  intro F E _ _ _ _ _ σ d d₁ W H' μ hμ 𝓕 f Ez s₀ R₀ hf hint hbd hreg hvan
  obtain ⟨hTG, -, hSC, -⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  intro ν 𝓕N hν hfd h1 h
  haveI : ContinuousMul (UA σ W.J) := inferInstance
  haveI : SecondCountableTopology (unip σ W H') := inferInstance
  haveI : FirstCountableTopology (unip σ W H') := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ this
  haveI : OpensMeasurableSpace (unip σ W H') := inferInstance
  haveI : OpensMeasurableSpace (UA σ W.J) := inferInstance
  have key : (fun s : ℂ => ∫ u in 𝓕N, ∫ h' in 𝓕, f h' * Ez s (u.1 * h) h' ∂μ ∂ν) s₀ = 0 := by
    refine eq_zero_of_locally_holo _ s₀ R₀ ?_ (fun s hs => (hvan s hs ν 𝓕N hν hfd h1 h).symm)
    intro s₁
    obtain ⟨k, r, C, N, Hf, hr, hk, hEq, hdiff, hcont, hHb⟩ := hreg s₁
    obtain ⟨Ch, hCh⟩ := hbd h
    haveI : IsFiniteMeasure (ν.restrict 𝓕N) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hCh0 : 0 ≤ Ch := le_trans (NNReal.coe_nonneg _) (hCh 1 (one_mem _))
    let B : UA σ W.J → ℝ := fun h' => |C| * Ch ^ N * (‖f h'‖ * (qht h' : ℝ) ^ N)
    have hBi : IntegrableOn B 𝓕 μ := (hint N).const_mul _
    have hnorm : ∀ s ∈ ball s₁ r, ∀ (u : unip σ W H') h', ‖f h' * Hf s (u.1 * h) h'‖ ≤ B h' := by
      intro s hs u h'
      rw [norm_mul]
      have h1' := hHb s hs (u.1 * h) h'
      have hq0 : 0 ≤ (qht (u.1 * h) : ℝ) * qht h' := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
      have hq : (qht (u.1 * h) : ℝ) * qht h' ≤ Ch * qht h' :=
        mul_le_mul_of_nonneg_right (hCh u.1 u.2) (NNReal.coe_nonneg _)
      have hp : ((qht (u.1 * h) : ℝ) * qht h') ^ N ≤ (Ch * qht h') ^ N := pow_le_pow_left₀ hq0 hq N
      have hC : C * ((qht (u.1 * h) : ℝ) * qht h') ^ N ≤ |C| * (Ch * qht h') ^ N :=
        calc C * ((qht (u.1 * h) : ℝ) * qht h') ^ N ≤ |C| * ((qht (u.1 * h) : ℝ) * qht h') ^ N :=
              mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hq0 N)
          _ ≤ |C| * (Ch * qht h') ^ N := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      calc ‖f h'‖ * ‖Hf s (u.1 * h) h'‖ ≤ ‖f h'‖ * (|C| * (Ch * qht h') ^ N) :=
            mul_le_mul_of_nonneg_left (h1'.trans hC) (norm_nonneg _)
        _ = B h' := by simp only [B]; rw [mul_pow]; ring
    have hGD := differentiableOn_integral_integral (ν.restrict 𝓕N) (μ.restrict 𝓕) (fun u : unip σ W H' => u.1 * h)
      (continuous_subtype_val.mul continuous_const) f hf Hf isOpen_ball hdiff hcont B hBi (fun s hs x y => hnorm s hs x y)
    refine ⟨k, r, _, hr, hk, hGD, fun s hs hsk => ?_⟩
    have hE := hEq s hs hsk
    simp only [hE, mul_left_comm (f _), integral_const_mul]
  exact key.symm

end GlobalTheory.CuspCont

end
