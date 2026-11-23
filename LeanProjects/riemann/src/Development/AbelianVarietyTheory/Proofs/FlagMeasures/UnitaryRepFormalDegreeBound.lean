import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCutoffFibreIntegralOneSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneParameterConjugationBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusModulusUnipotentRadicalUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryRepMatrixCoefficientBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffEqZeroOfLipschitzUnitaryFlowDecayStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarSubgroupBiInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalVolumeGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecayOfMemSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanDecay

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.ConstTermZero

section General

variable {G : Type} [Group G] [TopologicalSpace G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_zero_of_cutoff [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : Set G) (ν : Measure G)
    (hν : IsHaarSub N ν) (β : G → ENNReal) (hβ : Measurable β) (hβt : ∀ y, β y ≠ ⊤)
    (hβ1 : ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1) (F : G → ℂ) (hF : Continuous F)
    (hinv : ∀ m ∈ N, ∀ g, F (m * g) = F g)
    (h0 : (fun g => ((β g).toReal : ℂ) * (F g * star (F g))) =ᵐ[μ] 0) : ∀ g, F g = 0 := by
  haveI := hν.2.1
  have hFm : Measurable fun g => ‖F g‖ₑ := hF.measurable.enorm
  have h1 : ∫⁻ g, β g * ‖F g‖ₑ ∂μ = 0 := by
    refine (lintegral_eq_zero_iff (hβ.mul hFm)).2 ?_
    filter_upwards [h0] with g hg
    simp only [Pi.zero_apply, Pi.mul_apply, mul_eq_zero, Complex.ofReal_eq_zero, ENNReal.toReal_eq_zero_iff, hβt g, or_false,
      star_eq_zero, or_self] at hg ⊢
    rcases hg with h | h
    · exact Or.inl h
    · right; simp [h]
  have h2 : ∀ m ∈ N, ∫⁻ g, β (m⁻¹ * g) * ‖F g‖ₑ ∂μ = 0 := by
    intro m hm
    rw [← lintegral_mul_left_eq_self _ m, ← h1]
    simp only [inv_mul_cancel_left, hinv m hm]
  have hN : ∀ᵐ m ∂ν, m ∈ N := hν.2.2.1
  have h3 : ∫⁻ m, ∫⁻ g, β (m⁻¹ * g) * ‖F g‖ₑ ∂μ ∂ν = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0) (hN.mono fun m hm => h2 m hm)]
    simp
  have hmeas : Measurable (Function.uncurry fun m g : G => β (m⁻¹ * g) * ‖F g‖ₑ) :=
    (hβ.comp (measurable_fst.inv.mul measurable_snd)).mul (hFm.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable] at h3
  have h4 : ∫⁻ g, ‖F g‖ₑ ∂μ = 0 := by
    rw [← h3]
    refine lintegral_congr fun g => ?_
    rw [lintegral_mul_const (f := fun m => β (m⁻¹ * g)) _ (hβ.comp (measurable_inv.mul_const g)), hβ1, one_mul]
  rw [lintegral_eq_zero_iff hFm] at h4
  have h5 : F =ᵐ[μ] 0 := by
    filter_upwards [h4] with g hg
    simpa using hg
  exact congrFun ((hF.ae_eq_iff_eq μ continuous_const).1 h5)

def Decays (ρ : G → (H →L[ℂ] H)) (D : G → ℝ) (c : ℝ) (v u : H) : Prop :=
  ∃ C : ℝ, ∀ g : G, ‖⟪v, ρ g u⟫_ℂ‖ ≤ C * Real.exp (-(c * D g))

theorem inner_move {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) (x : G) (v u : H) :
    ⟪ρ x v, u⟫_ℂ = ⟪v, ρ x⁻¹ u⟫_ℂ := by
  have e : ρ x (ρ x⁻¹ u) = u := by
    have := congrArg (fun T : H →L[ℂ] H => T u) (hρ.2.1 x x⁻¹)
    simp only [mul_inv_cancel, hρ.1] at this
    simpa using this.symm
  let f : H →ₗᵢ[ℂ] H := ⟨(ρ x : H →ₗ[ℂ] H), hρ.2.2.1 x⟩
  have := f.inner_map_map v (ρ x⁻¹ u)
  rw [← this]
  show _ = ⟪ρ x v, ρ x (ρ x⁻¹ u)⟫_ℂ
  rw [e]

omit [TopologicalSpace G] in

theorem act_mul [TopologicalSpace G] {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) (x y : G) (u : H) :
    ρ (x * y) u = ρ x (ρ y u) := by
  rw [hρ.2.1]; rfl

omit [Group G] [TopologicalSpace G] in

theorem decays_span_left {ρ : G → (H →L[ℂ] H)} {D : G → ℝ} {c : ℝ} {S : Set H} {u : H}
    (h : ∀ v ∈ S, Decays ρ D c v u) : ∀ v ∈ Submodule.span ℂ S, Decays ρ D c v u := by
  first
  | exact @_root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span
  | exact _root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span
  | (apply _root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DecayOfMemSpan.decay_of_mem_span ..)

omit [Group G] [TopologicalSpace G] in

theorem decays_span_right {ρ : G → (H →L[ℂ] H)} {D : G → ℝ} {c : ℝ} {S : Set H} {v : H}
    (h : ∀ u ∈ S, Decays ρ D c v u) : ∀ u ∈ Submodule.span ℂ S, Decays ρ D c v u := by
  first
  | exact @_root_.GlobalTheory.SpanDecay.span_decay
  | exact _root_.GlobalTheory.SpanDecay.span_decay
  | (apply _root_.GlobalTheory.SpanDecay.span_decay <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpanDecay.span_decay <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpanDecay.span_decay <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpanDecay.span_decay ..)

theorem decays_translate {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {D : G → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ g g', D (g * g') ≤ D g + D g') {v u : H} (h : Decays ρ D c v u) (x y : G) :
    Decays ρ D c (ρ x v) (ρ y u) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine ⟨C * Real.exp (c * (D x + D y⁻¹)), fun g => ?_⟩
  rw [inner_move hρ, ← act_mul hρ, ← act_mul hρ]
  refine (hC _).trans ?_
  rw [mul_assoc C, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0
  have h1 := hD x (x⁻¹ * g * y * y⁻¹)
  have h2 := hD (x⁻¹ * g * y) y⁻¹
  have e : x * (x⁻¹ * g * y * y⁻¹) = g := by group
  rw [e] at h1
  have : c * D g ≤ c * (D x + D y⁻¹ + D (x⁻¹ * g * y)) := mul_le_mul_of_nonneg_left (by linarith) hc
  nlinarith

theorem decays_orbit {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {D : G → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hD : ∀ g g', D (g * g') ≤ D g + D g') {w : H} (h : Decays ρ D c w w) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun g => ρ g w), ∀ u ∈ Submodule.span ℂ (Set.range fun g => ρ g w),
      Decays ρ D c v u := by
  intro v hv u hu
  refine decays_span_left ?_ v hv
  rintro _ ⟨x, rfl⟩
  refine decays_span_right ?_ u hu
  rintro _ ⟨y, rfl⟩
  exact decays_translate hρ hc hD h x y

theorem orbit_stable {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) (w : H) (x : G) :
    ∀ v ∈ Submodule.span ℂ (Set.range fun g => ρ g w), ρ x v ∈ Submodule.span ℂ (Set.range fun g => ρ g w) := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, rfl⟩ := hy
    exact Submodule.subset_span ⟨x * g, act_mul hρ x g w⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [map_smul]; exact Submodule.smul_mem _ _ hb

theorem form_add_le {V : Type} [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (h : ∀ x, 0 ≤ I x x)
    (x y : V) (a b : ℝ) :
    (I ((a : ℂ) • x + (b : ℂ) • y) ((a : ℂ) • x + (b : ℂ) • y)).re ≤
      2 * a ^ 2 * (I x x).re + 2 * b ^ 2 * (I y y).re := by
  have h1 := (Complex.nonneg_iff.1 (h ((a : ℂ) • x - (b : ℂ) • y))).1
  simp only [map_add, map_sub, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, Complex.conj_ofReal, Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul,
    RingHom.id_apply] at h1 ⊢
  nlinarith

end General

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem integral_conj {ν : Measure G} {x : G} {t : ℝ}
    (h : ν.map (fun m => x * m * x⁻¹) = ENNReal.ofReal (Real.exp t) • ν) (f : G → ℂ) (hf : Continuous f) :
    ∫ m, f (x * m * x⁻¹) ∂ν = (Real.exp t : ℂ) * ∫ m, f m ∂ν := by
  have hm : Measurable fun m : G => x * m * x⁻¹ := (measurable_const_mul x).mul_const _
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, h, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos t).le, Complex.real_smul]

omit [IsTopologicalGroup G] in

theorem Decays.integrable {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {D : G → ℝ} {c : ℝ} {ν : Measure G}
    (hi : Integrable (fun m => Real.exp (-(c * D m))) ν) {v u : H} (h : Decays ρ D c v u) :
    Integrable (fun m => ⟪v, ρ m u⟫_ℂ) ν := by
  obtain ⟨C, hC⟩ := h
  have hc : Continuous fun g => ⟪v, ρ g u⟫_ℂ := continuous_const.inner (hρ.2.2.2 u)
  exact (hi.const_mul C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hC)

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [Group G] in

theorem exists_form (ρ : G → (H →L[ℂ] H)) (ν : Measure G) (V : Submodule ℂ H)
    (hi : ∀ v ∈ V, ∀ u ∈ V, Integrable (fun m => ⟪v, ρ m u⟫_ℂ) ν) :
    ∃ I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, ∀ v u : V, I v u = ∫ m, ⟪(v : H), ρ m u⟫_ℂ ∂ν := by
  refine ⟨LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v u : V => ∫ m, ⟪(v : H), ρ m u⟫_ℂ ∂ν)
    (fun x x' y => ?_) (fun c x y => ?_) (fun x y y' => ?_) (fun c x y => ?_), fun _ _ => rfl⟩
  · simp only [Submodule.coe_add, inner_add_left]
    exact integral_add (hi _ x.2 _ y.2) (hi _ x'.2 _ y.2)
  · simp only [Submodule.coe_smul, inner_smul_left, smul_eq_mul, integral_const_mul]
  · simp only [Submodule.coe_add, map_add, inner_add_right]
    exact integral_add (hi _ x.2 _ y.2) (hi _ x.2 _ y'.2)
  · simp only [Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply, integral_const_mul]

omit [IsTopologicalGroup G] in

theorem torus_decay {ρ : G → (H →L[ℂ] H)} {D : G → ℝ} {c : ℝ} (hc : 0 ≤ c) {ν : Measure G} {N : Set G}
    (hN : ν Nᶜ = 0) (hD : ∀ g g', D (g * g') ≤ D g + D g') (hDi : ∀ g, D g⁻¹ = D g)
    (hi : Integrable (fun m => Real.exp (-(c / 3 * D m))) ν) {a : ℝ → G} (ha : ∀ s, D (a s) ≤ |s|)
    (ha' : ∀ s, ∀ m ∈ N, |s| ≤ D (m * a s)) {v : H} (h : Decays ρ D c v v) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s, ‖∫ m, ⟪v, ρ (m * a s) v⟫_ℂ ∂ν‖ ≤ A * Real.exp (-(c / 3 * |s|)) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  refine ⟨C * ∫ m, Real.exp (-(c / 3 * D m)) ∂ν,
    mul_nonneg hC0 (integral_nonneg fun _ => (Real.exp_pos _).le), fun s => ?_⟩
  rw [← integral_const_mul, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((hi.const_mul C).mul_const _) ?_
  have hN' : ∀ᵐ m ∂ν, m ∈ N := hN
  filter_upwards [hN'] with m hm
  refine (hC _).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0
  have h1 := hD (m * a s) (a s)⁻¹
  rw [mul_inv_cancel_right, hDi] at h1
  have h2 := ha s
  have h3 := ha' s m hm
  have : c / 3 * (D m + |s|) ≤ c / 3 * (3 * D (m * a s)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

theorem exp_sub_one_sq_le (k : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, |s| ≤ 1 →
    Real.exp (k * s) ^ 2 ≤ K ∧ (Real.exp (k * s) - 1) ^ 2 ≤ K * s ^ 2 := by
  refine ⟨Real.exp |k| ^ 2 * (1 + k ^ 2), by positivity, fun s hs => ?_⟩
  have h1 : |k * s| ≤ |k| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs
  have h2 : Real.exp (k * s) ≤ Real.exp |k| := Real.exp_le_exp.2 ((le_abs_self _).trans h1)
  have h3 : 1 ≤ Real.exp |k| := Real.one_le_exp (abs_nonneg _)
  have h4 : Real.exp (k * s) ^ 2 ≤ Real.exp |k| ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le h2 2
  refine ⟨h4.trans (le_mul_of_one_le_right (by positivity) (by nlinarith [sq_nonneg k])), ?_⟩
  have h5 : |Real.exp (k * s) - 1| ≤ Real.exp |k| * |k * s| := by
    set x := k * s
    have a1 := Real.add_one_le_exp x
    have a2 := Real.add_one_le_exp (-x)
    have a3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    have a4 := Real.exp_pos x
    have a5 := le_abs_self x
    have a6 := neg_abs_le x
    have a7 := abs_nonneg x
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left a2 a4.le, mul_le_mul_of_nonneg_right h2 a7,
        mul_le_mul_of_nonneg_left a5 a4.le]
  have h6 := pow_le_pow_left₀ (abs_nonneg _) h5 2
  rw [sq_abs, mul_pow, sq_abs] at h6
  nlinarith [mul_nonneg (sq_nonneg (Real.exp |k|)) (sq_nonneg s)]

end Main

section Flow

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem form_zero {ρ : G → (H →L[ℂ] H)} (hρ : IsURep ρ) {D : G → ℝ} {c τ r κ C₀ : ℝ} (hτ : 0 ≤ τ) (hc : 3 * τ < c)
    (hr : 0 < r) (hκ : |κ| ≤ 2 * τ) {μ ν : Measure G} {N : Set G} (hN : ν Nᶜ = 0)
    (hD : ∀ g g', D (g * g') ≤ D g + D g') (hDi : ∀ g, D g⁻¹ = D g)
    (hi : ∀ b, τ < b → Integrable (fun m => Real.exp (-(b * D m))) ν) {a : ℝ → G}
    (ha0 : a 0 = 1) (hadd : ∀ s t, a (s + t) = a s * a t) (ha : ∀ s, D (a s) ≤ |s|)
    (ha' : ∀ s, ∀ m ∈ N, |s| ≤ D (m * a s))
    (hmod : ∀ s, ν.map (fun m => a s * m * (a s)⁻¹) = ENNReal.ofReal (Real.exp (κ * s)) • ν)
    (V : Submodule ℂ H) (hV : ∀ g, ∀ v ∈ V, ρ g v ∈ V) (hdec : ∀ v ∈ V, ∀ u ∈ V, Decays ρ D c v u)
    {w : H} (hw : w ∈ V) (β : G → ENNReal)
    (hnorm : ∀ v ∈ V, ∫ g, ((β g).toReal : ℂ) * ((∫ m, ⟪v, ρ (m * g) w⟫_ℂ ∂ν) *
      star (∫ m, ⟪v, ρ (m * g) w⟫_ℂ ∂ν)) ∂μ = (∫ m, ⟪v, ρ m v⟫_ℂ ∂ν) * (r : ℂ))
    (hlip : ∀ v ∈ V, ∀ s : ℝ, |s| ≤ 1 → ∫ g, (β g).toReal * ‖(∫ m, ⟪v, ρ (m * (a s * g)) w⟫_ℂ ∂ν) -
      (∫ m, ⟪v, ρ (m * g) w⟫_ℂ ∂ν)‖ ^ 2 ∂μ ≤ C₀ * s ^ 2 * (∫ m, ⟪v, ρ m v⟫_ℂ ∂ν).re) :
    ∀ v ∈ V, ∫ m, ⟪v, ρ m v⟫_ℂ ∂ν = 0 := by
  have hc0 : 0 ≤ c := by linarith
  have hint : ∀ v ∈ V, ∀ u ∈ V, Integrable (fun m => ⟪v, ρ m u⟫_ℂ) ν := fun v hv u hu =>
    (hdec v hv u hu).integrable hρ (hi c (by linarith))
  obtain ⟨I, hI⟩ := exists_form ρ ν V hint
  have hainv : ∀ s, (a s)⁻¹ = a (-s) := fun s => by
    rw [inv_eq_iff_mul_eq_one, ← hadd, add_neg_cancel, ha0]

  have hnorm' : ∀ v : V, I v v = (((∫ g, (β g).toReal * ‖∫ m, ⟪(v : H), ρ (m * g) w⟫_ℂ ∂ν‖ ^ 2 ∂μ) / r : ℝ) : ℂ) := by
    intro v
    have h := hnorm v v.2
    rw [hI, Complex.ofReal_div, eq_div_iff (by exact_mod_cast hr.ne'), ← h, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; rfl
  have hpos : ∀ v : V, 0 ≤ I v v := by
    intro v
    rw [hnorm']
    exact_mod_cast div_nonneg (integral_nonneg fun g => by positivity) hr.le

  let R : G → V →ₗ[ℂ] V := fun g => (ρ g : H →ₗ[ℂ] H).restrict (hV g)
  have hR : ∀ g (v : V), ((R g v : V) : H) = ρ g v := fun _ _ => rfl
  have key : ∀ s (x : H) (u : H), ∫ m, ⟪ρ (a s) x, ρ m u⟫_ℂ ∂ν =
      (Real.exp (κ * (-s)) : ℂ) * ∫ m, ⟪x, ρ m (ρ (a (-s)) u)⟫_ℂ ∂ν := by
    intro s x u
    rw [← integral_conj (hmod (-s)) (fun m => ⟪x, ρ m (ρ (a (-s)) u)⟫_ℂ) (continuous_const.inner (hρ.2.2.2 _))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
    simp only []
    rw [inner_move hρ, ← act_mul hρ, ← act_mul hρ, hainv, inv_mul_cancel_right]
  let U : ℝ → V →ₗ[ℂ] V := fun s => ((Real.exp (κ / 2 * s) : ℝ) : ℂ) • R (a s)
  have hU : ∀ s (v : V), U s v = ((Real.exp (κ / 2 * s) : ℝ) : ℂ) • R (a s) v := fun _ _ => rfl
  intro v hv
  rw [← hI ⟨v, hv⟩ ⟨v, hv⟩]
  obtain ⟨K, hK0, hK⟩ := exp_sub_one_sq_le (-(κ / 2))
  refine GlobalTheory.T.coeff_eq_zero_of_lipschitz_unitary_flow_decay V I U (2 * K * (|C₀| / r) + 2 * K) ⟨v, hv⟩ hpos ?_ ?_ ?_ ?_ ?_
  · ext x
    simp [hU, hR, ha0, hρ.1]
  · intro s t
    ext x
    simp only [LinearMap.comp_apply, hU, map_smul, Submodule.coe_smul, hR, hadd, act_mul hρ, smul_smul, mul_add,
      Real.exp_add, Complex.ofReal_mul]
  · intro s x y
    simp only [hU, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, Complex.conj_ofReal,
      RingHom.id_apply]
    rw [hI, hI, hR, hR, key, ← act_mul hρ, ← hadd, neg_add_cancel, ha0, hρ.1, ← mul_assoc, ← mul_assoc,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    have : κ / 2 * s + κ / 2 * s + κ * -s = 0 := by ring
    rw [this, Real.exp_zero, Complex.ofReal_one, one_mul]
    rfl
  · intro s x hs
    set z : V := ((Real.exp (κ * s) : ℝ) : ℂ) • R (a s) x - x with hz
    have e1 : U s x - x = ((Real.exp (-(κ / 2) * s) : ℝ) : ℂ) • z +
        ((Real.exp (-(κ / 2) * s) - 1 : ℝ) : ℂ) • x := by
      rw [hz, hU, smul_sub, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_sub, sub_smul]
      have : -(κ / 2) * s + κ * s = κ / 2 * s := by ring
      rw [this]; simp
    have e2 : ∀ g, ∫ m, ⟪(z : H), ρ (m * g) w⟫_ℂ ∂ν =
        (∫ m, ⟪(x : H), ρ (m * (a (-s) * g)) w⟫_ℂ ∂ν) - ∫ m, ⟪(x : H), ρ (m * g) w⟫_ℂ ∂ν := by
      intro g
      have := hI z ⟨ρ g w, hV g w hw⟩
      simp only [act_mul hρ]
      rw [← this, hz]
      simp only [map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        Complex.conj_ofReal, hI, hR]
      rw [key, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      simp
    have e3 : (I z z).re ≤ |C₀| / r * s ^ 2 * (I x x).re := by
      have h := hlip x x.2 (-s) (by rwa [abs_neg])
      rw [← hI, neg_sq] at h
      have hx := (Complex.nonneg_iff.1 (hpos x)).1
      rw [hnorm' z, Complex.ofReal_re, div_le_iff₀ hr]
      simp only [e2]
      refine h.trans ?_
      have : |C₀| / r * s ^ 2 * (I x x).re * r = |C₀| * s ^ 2 * (I x x).re := by field_simp
      rw [this]
      gcongr
      exact le_abs_self _
    rw [e1]
    refine (form_add_le I hpos z x _ _).trans ?_
    have hx := (Complex.nonneg_iff.1 (hpos x)).1
    have hz0 := (Complex.nonneg_iff.1 (hpos z)).1
    obtain ⟨k1, k2⟩ := hK s hs
    have b1 : Real.exp (-(κ / 2) * s) ^ 2 * (I z z).re ≤ K * (|C₀| / r * s ^ 2 * (I x x).re) :=
      mul_le_mul k1 e3 hz0 hK0
    have b2 := mul_le_mul_of_nonneg_right k2 hx
    nlinarith
  · obtain ⟨A, hA0, hA⟩ := torus_decay hc0 hN hD hDi (hi (c / 3) (by linarith)) ha ha' (hdec v hv v hv)
    refine ⟨A, c / 3 - τ, by linarith, fun s => ?_⟩
    rw [hU, map_smul, smul_eq_mul, hI, hR, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have h := hA s
    simp only [act_mul hρ] at h
    refine (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le).trans ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA0
    have h1 : κ * s ≤ |κ| * |s| := by rw [← abs_mul]; exact le_abs_self _
    have h2 := mul_le_mul_of_nonneg_right hκ (abs_nonneg s)
    nlinarith

end Flow

theorem ae_zero_of_nonneg {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ} (hi : Integrable f μ)
    (h0 : ∀ x, 0 ≤ f x) (h : ∫ x, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have h1 : ∫ x, RCLike.re (f x) ∂μ = 0 := by rw [integral_re hi, h, map_zero]
  have h2 := (integral_eq_zero_iff_of_nonneg (fun x => (Complex.nonneg_iff.1 (h0 x)).1) hi.re).1 h1
  filter_upwards [h2] with x hx
  exact Complex.ext hx (Complex.nonneg_iff.1 (h0 x)).2.symm

theorem constant_term_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Fin n → ℂ)) (ν : Measure (UJ ε)), IsIsoC ε W → IsHaarSub (NW ε W) ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d c : ℝ) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → IsFdeg (muG ε) σ d → 12 * n * rkR ε < c → ‖w‖ = 1 → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → ∀ x y : UJ ε, ∫ m, ⟪w, σ (umat (x * m * y)) w⟫_ℂ ∂ν = 0 := by
  intro n ε W ν hW hν H _ _ _ σ d c α w hσ hd hc hw hα hαc hfix hdec x y
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim _ _) hW.1
    · exact h
  let ρ : UJ ε → (H →L[ℂ] H) := fun g => σ (umat g)
  let D : UJ ε → ℝ := fun g => dOp (umat g)
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hcu : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
  have hρ : IsURep ρ := ⟨hσ.1.1, fun a b => hσ.1.2 _ (hmem a) _ (hmem b), fun g => hσ.2.1 _ (hmem g),
    fun v => (hσ.2.2 v).comp_continuous hcu hmem⟩
  have hD : ∀ g g', D (g * g') ≤ D g + D g' := fun g g' =>
    ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g' hn).2.2.1
  have hDi : ∀ g, D g⁻¹ = D g := fun g => ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).2.1
  have hq : (0 : ℝ) ≤ n * rkR ε := by positivity
  have hc0 : 0 ≤ c := by linarith
  have hc8 : 8 * (n : ℝ) * rkR ε < c := by linarith
  obtain ⟨β, hβ, hβt, hβ1⟩ := GlobalTheory.T.exists_measurable_cutoff_fibre_integral_one_subgroup (UJ ε) (nwSub ε W) ν (isClosed_NW ε W) hν
  obtain ⟨a, Hm, hHm, haH, ha, ha', -, hiw⟩ := GlobalTheory.T.isotropic_splitTorus_iwasawa_unitaryGroup n ε W hW
  obtain ⟨κ, hκ, hmod⟩ := GlobalTheory.T.torus_modulus_unipotentRadical_unitaryGroup n ε W ν hW hν a Hm hHm haH ha fun s m hm => (ha' s m hm).1
  obtain ⟨L, hL⟩ := GlobalTheory.T.hasDerivAt_orbit_and_decay_of_decay n ε H σ α w hσ hα hαc hfix
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.one_parameter_conjugation_bound n ε W ν hW hν β hβ hβt hβ1 a Hm hHm haH hiw κ hmod H σ d c w L hσ hd hc8
    fun X hX => (hL X hX).1
  have hright := (GlobalTheory.T.haar_subgroup_bi_invariant n ε W ν hW hν).1
  have hvol := (GlobalTheory.T.unipotentRadical_volume_growth n ε W ν hW hν).2
  let V : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => ρ g w)
  have hVd : ∀ v ∈ V, ∀ u ∈ V, Decays ρ D c v u := decays_orbit hρ hc0 hD hdec
  have hwV : w ∈ V := Submodule.subset_span ⟨1, by simp [hρ.1]⟩
  have hnorm := fun v (hv : v ∈ V) => GlobalTheory.T.unitary_rep_matrix_coefficient_bound n ε W ν hW hν β hβ hβt hβ1 H σ d c w v v hσ hd hc8
    (hVd v hv w hwV) (hVd v hv w hwV) (hVd v hv v hv)
  have ha0 : a 0 = 1 := by
    refine Subtype.ext (Units.ext ?_)
    have := haH 0
    simpa using this
  have hadd : ∀ s t, a (s + t) = a s * a t := by
    intro s t
    refine Subtype.ext (Units.ext ?_)
    show umat (a (s + t)) = umat (a s) * umat (a t)
    rw [haH, haH, haH, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl Hm).smul_left _).smul_right _)
  have hzero := form_zero (μ := muG ε) (ν := ν) (N := NW ε W) (C₀ := C₀) (r := ‖w‖ ^ 2 / d) (τ := 4 * n * rkR ε)
    (κ := κ) (c := c) (D := D) hρ (by linarith) (by linarith) (by rw [hw]; have := hd.1; positivity) (by linarith)
    hν.2.2.1 hD hDi hvol ha0 hadd ha (fun s m hm => (ha' s m hm).2) hmod V (orbit_stable hρ w) hVd hwV β
    (fun v hv => (hnorm v hv).2.2)
    (fun v hv => hC₀ v (hVd v hv w hwV) (hVd v hv v hv) fun X hX => (hL X hX).2 c v hc0 (hVd v hv w hwV))
  have hv : ρ x⁻¹ w ∈ V := Submodule.subset_span ⟨x⁻¹, rfl⟩
  set v := ρ x⁻¹ w with hvdef
  obtain ⟨h1, h2, h3⟩ := hnorm v hv
  have h4 := hzero v hv
  have hF := eq_zero_of_cutoff (muG ε) (NW ε W) ν hν β hβ hβt hβ1 _ h1 ?_ ?_ y
  · rw [← hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
    show ⟪w, ρ (x * m * y) w⟫_ℂ = ⟪ρ x⁻¹ w, ρ (m * y) w⟫_ℂ
    rw [inner_move hρ, inv_inv, ← act_mul hρ, mul_assoc]
  · intro m hm g
    have hcf : Continuous fun k : UJ ε => ⟪v, ρ (k * g) w⟫_ℂ :=
      continuous_const.inner ((hρ.2.2.2 w).comp (continuous_mul_const g))
    have := integral_map (μ := ν) (measurable_mul_const m).aemeasurable hcf.aestronglyMeasurable
    rw [hright m hm] at this
    simp only [mul_assoc] at this
    exact this.symm
  · refine ae_zero_of_nonneg h2 (fun g => ?_) ?_
    · exact mul_nonneg (by exact_mod_cast ENNReal.toReal_nonneg) (mul_star_self_nonneg _)
    · rw [h3]
      exact mul_eq_zero_of_left h4 _

end GlobalTheory.ConstTermZero
