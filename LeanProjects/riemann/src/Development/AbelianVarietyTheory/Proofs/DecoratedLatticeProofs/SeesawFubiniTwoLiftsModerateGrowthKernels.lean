import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecrStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralKernelLiftsFubiniSigmaFiniteStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Seesaw

variable {D : D7}

theorem out_eq_sec {V : HSp D} {X : Type*} {φ : GA D V → X} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (q : AutQ V) :
    φ q.out = φ (sec (GQ V) q) :=
  LeftInv.eq_of_mk_eq (Γ := GQ V) h ((Quotient.out_eq q).trans (mk_sec q).symm)

theorem measurable_out {V : HSp D} {φ : GA D V → ℂ} (h : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) (hc : Continuous φ) :
    Measurable fun q : AutQ V => φ q.out := by
  have e : (fun q : AutQ V => φ q.out) = φ ∘ sec (GQ V) := funext (out_eq_sec h)
  rw [e]
  exact hc.measurable.comp measurableEmbedding_sec.measurable

theorem measurable_kernel_out {A B : HSp D} {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K))
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hr : ∀ g, ∀ γ ∈ GQ B, ∀ h, K g (γ * h) = K g h) :
    Measurable (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) := by
  have e : (Function.uncurry fun (q : AutQ A) (y : AutQ B) => K q.out y.out) =
      Function.uncurry K ∘ fun p => (sec (GQ A) p.1, sec (GQ B) p.2) := by
    funext p
    show K p.1.out p.2.out = K (sec (GQ A) p.1) (sec (GQ B) p.2)
    rw [out_eq_sec (φ := fun g => K g p.2.out) (fun γ hγ g => hl γ hγ g _) p.1, out_eq_sec (hr _) p.2]
  rw [e]
  exact hc.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_fst).prodMk
    (measurableEmbedding_sec.measurable.comp measurable_snd))

theorem integrable_lift_integrand {A B : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure)
    {K : GA D A → GA D B → ℂ} (hc : Continuous (Function.uncurry K)) (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h)
    (hg : ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) {u : GA D A → ℂ} (hu : GlobalTheory.Grow.RapidDec A u) (h : GA D B) :
    Integrable (descend (GQ A) fun g => K g h * u g) (autMeasure A m) := by
  obtain ⟨C, a, hC⟩ := hg h
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => K g h) (fun γ hγ g => hl γ hγ g h) hC
  have hKc : Continuous fun g => K g h := hc.comp (continuous_id.prodMk continuous_const)
  have hmeas : Measurable (descend (GQ A) fun g => K g h * u g) :=
    measurable_out (φ := fun g => K g h * u g) (fun γ hγ g => by simp only [hl γ hγ, hu.1 γ hγ]) (hKc.mul hu.2.1)
  refine ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu a).const_mul (C * 2 ^ a)).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun q => ?_)
  show ‖K q.out h * u q.out‖ ≤ C * 2 ^ a * (GlobalTheory.Grow.quotHeight A q.out ^ a * ‖u q.out‖)
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)

theorem lintegral_slice_le {A B : HSp D} (mH : Measure (GA D B)) {K : GA D A → GA D B → ℂ}
    (hl : ∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) (hL2 : ∀ g, MemL2Quotient (GQ B) mH (K g))
    (hP : GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) :
    ∃ (c : ℝ) (a : ℕ), 0 ≤ c ∧ ∀ g, ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH ≤
      ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A g ^ a) := by
  obtain ⟨C, a, hC⟩ := hP
  have hinv : ∀ γ ∈ GQ A, ∀ g, petersson B mH (K (γ * g)) (K (γ * g)) = petersson B mH (K g) (K g) :=
    fun γ hγ g => by rw [show K (γ * g) = K g from funext (hl γ hγ g)]
  refine ⟨C * 2 ^ a, a, mul_nonneg (GlobalTheory.Grow.nonneg_of_growth hC) (by positivity), fun g => ?_⟩
  have hb := GlobalTheory.Grow.norm_le_quotHeight_pow hinv hC g
  have hf := (hL2 g).2
  have hf2 : Integrable (fun y : AutQ B => ‖K g y.out‖ ^ 2) (autMeasure B mH) :=
    (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have e1 : ∫⁻ y, ‖K g y.out‖ₑ ^ 2 ∂autMeasure B mH = ENNReal.ofReal (∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH) := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (ae_of_all _ fun _ => by positivity)]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have e2 : petersson B mH (K g) (K g) = ((∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    show ∫ y, descend (GQ B) (K g) y * conj (descend (GQ B) (K g) y) ∂autMeasure B mH = _
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show K g y.out * conj (K g y.out) = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e3 : ‖petersson B mH (K g) (K g)‖ = ∫ y, ‖K g y.out‖ ^ 2 ∂autMeasure B mH := by
    rw [e2, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => by positivity)]
  rw [e1]
  exact ENNReal.ofReal_le_ofReal (e3 ▸ hb)

theorem weight_data {A : HSp D} (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {u : GA D A → ℂ}
    (hu : GlobalTheory.Grow.RapidDec A u) {c : ℝ} (hc : 0 ≤ c) (a : ℕ) :
    (∀ q : AutQ A, ENNReal.ofReal (c * GlobalTheory.Grow.quotHeight A q.out ^ a) ≤
      ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) ^ 2) ∧
    ∫⁻ q, ENNReal.ofReal (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖ₑ ∂autMeasure A m ≠ ⊤ := by
  have ht : ∀ q : AutQ A, 0 ≤ c * GlobalTheory.Grow.quotHeight A q.out ^ a :=
    fun q => mul_nonneg hc (pow_nonneg (GlobalTheory.Grow.quotHeight_pos A _).le _)
  refine ⟨fun q => ?_, ?_⟩
  · rw [← ENNReal.ofReal_pow (by linarith [ht q])]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [ht q])
  · have hint : Integrable (fun q : AutQ A => (1 + c * GlobalTheory.Grow.quotHeight A q.out ^ a) * ‖u q.out‖)
        (autMeasure A m) := by
      refine ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu 0).add ((GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D A m hm u hu a).const_mul c)).congr
        (ae_of_all _ fun q => ?_)
      simp only [Pi.add_apply, pow_zero, one_mul]
      ring
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hint.lintegral_lt_top)
    refine lintegral_congr fun q => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by linarith [ht q])]

theorem seesaw_fubini : ∀ (D : D7) (A B : HSp D) (m : Measure (GA D A)) (mH : Measure (GA D B)), m.IsHaarMeasure → mH.IsHaarMeasure → ∀ K₁ K₂ : GA D A → GA D B → ℂ, (∀ K ∈ ({K₁, K₂} : Set (GA D A → GA D B → ℂ)), Continuous (Function.uncurry K) ∧ (∀ γ ∈ GQ A, ∀ g h, K (γ * g) h = K g h) ∧ (∀ g, MemL2Quotient (GQ B) mH (K g)) ∧ (GlobalTheory.Grow.ModGrowth A fun g => petersson B mH (K g) (K g)) ∧ ∀ h, GlobalTheory.Grow.ModGrowth A fun g => K g h) → ∀ u₁ u₂ : GA D A → ℂ, GlobalTheory.Grow.RapidDec A u₁ → GlobalTheory.Grow.RapidDec A u₂ → let θ₁ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₁ g h * u₁ g) q ∂autMeasure A m; let θ₂ : GA D B → ℂ := fun h => ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ A) (fun g => K₂ g h * u₂ g) q ∂autMeasure A m; (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₁ g h * u₁ g) (autMeasure A m)) ∧ (∀ h, Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ A) fun g => K₂ g h * u₂ g) (autMeasure A m)) ∧ MemL2Quotient (GQ B) mH θ₁ ∧ MemL2Quotient (GQ B) mH θ₂ ∧ petersson B mH θ₁ θ₂ = ∫ q : AutQ A × AutQ A, petersson B mH (K₁ q.1.out) (K₂ q.2.out) * u₁ q.1.out * conj (u₂ q.2.out) ∂(autMeasure A m).prod (autMeasure A m) := by
  intro D A B m mH hm hmH K₁ K₂ hK u₁ u₂ hu₁ hu₂ θ₁ θ₂
  obtain ⟨hc₁, hl₁, hL₁, hP₁, hg₁⟩ := hK K₁ (Set.mem_insert _ _)
  obtain ⟨hc₂, hl₂, hL₂, hP₂, hg₂⟩ := hK K₂ (Set.mem_insert_of_mem _ rfl)
  have hi₁ := integrable_lift_integrand m hm hc₁ hl₁ hg₁ hu₁
  have hi₂ := integrable_lift_integrand m hm hc₂ hl₂ hg₂ hu₂
  have hr₁ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₁ g (γ * h) = K₁ g h := fun g => (hL₁ g).1
  have hr₂ : ∀ g, ∀ γ ∈ GQ B, ∀ h, K₂ g (γ * h) = K₂ g h := fun g => (hL₂ g).1
  obtain ⟨c₁, a₁, hc₁0, hs₁⟩ := lintegral_slice_le mH hl₁ hL₁ hP₁
  obtain ⟨c₂, a₂, hc₂0, hs₂⟩ := lintegral_slice_le mH hl₂ hL₂ hP₂
  obtain ⟨hw₁, hf₁⟩ := weight_data m hm hu₁ hc₁0 a₁
  obtain ⟨hw₂, hf₂⟩ := weight_data m hm hu₂ hc₂0 a₂
  have := hm
  have := hmH
  have key := GlobalTheory.T.integral_kernel_lifts_fubini_sigmaFinite (autMeasure A m) (autMeasure A m) (autMeasure B mH)
    (fun q y => K₁ q.out y.out) (fun q y => K₂ q.out y.out) (fun q => u₁ q.out) (fun q => u₂ q.out)
    (measurable_kernel_out hc₁ hl₁ hr₁) (measurable_kernel_out hc₂ hl₂ hr₂)
    (measurable_out hu₁.1 hu₁.2.1) (measurable_out hu₂.1 hu₂.2.1) _ _
    (fun q => (hs₁ q.out).trans (hw₁ q)) (fun q => (hs₂ q.out).trans (hw₂ q)) hf₁ hf₂
    (fun y => hi₁ y.out) (fun y => hi₂ y.out)
  have inv₁ : ∀ γ ∈ GQ B, ∀ h, θ₁ (γ * h) = θ₁ h := fun γ hγ h => by
    have e : (fun g => K₁ g (γ * h) * u₁ g) = fun g => K₁ g h * u₁ g := funext fun g => by rw [hr₁ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₁ g (γ * h) * u₁ g) q ∂autMeasure A m = _
    rw [e]
  have inv₂ : ∀ γ ∈ GQ B, ∀ h, θ₂ (γ * h) = θ₂ h := fun γ hγ h => by
    have e : (fun g => K₂ g (γ * h) * u₂ g) = fun g => K₂ g h * u₂ g := funext fun g => by rw [hr₂ g γ hγ h]
    show ∫ q, descend (GQ A) (fun g => K₂ g (γ * h) * u₂ g) q ∂autMeasure A m = _
    rw [e]
  exact ⟨hi₁, hi₂, ⟨inv₁, key.1⟩, ⟨inv₂, key.2.1⟩, key.2.2⟩

end GlobalTheory.Core.Rk.Seesaw

end
