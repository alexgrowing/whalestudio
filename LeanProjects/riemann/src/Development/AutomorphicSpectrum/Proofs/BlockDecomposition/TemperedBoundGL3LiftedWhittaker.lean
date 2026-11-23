import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.GTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionGlTwoHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaRegionMeasureBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeometricSumBelowThreshold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierTransformIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerCentral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalWhittakerSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerIwasawaGrowthBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDoubleIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalTorusReduction

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel ENNReal

namespace GlobalTheory.CompanionTheory.LFTempered

theorem whittaker_bound_iwasawa (e : ℝ) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (ψ : AddChar F Circle) (W' : GL (Fin 2) F → ℂ) (C : ℝ), (∀ x g, W' (Ad3.uni2 x * g) = (ψ x : ℂ) * W' g) → (∀ (a : Fˣ) g, W' (Ad3.dg2 a a * g) = W' g) → (∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 a 1 * κ)‖ ≤ C * (modulus (a : F) : ℝ) ^ e) → ∀ (t₁ t₂ b₁ b₂ : Fˣ) (x : F), ∀ κ ∈ GLnLocal.integralGL F 2, ‖W' (Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ))‖ ≤ C * (modulus ((t₁ * b₁ * (t₂ * b₂)⁻¹ : Fˣ) : F) : ℝ) ^ e := by
  intro F _ _ _ _ ψ W' C hu hd hb t₁ t₂ b₁ b₂ x κ hκ
  have e' : Ad3.dg2 t₁ t₂ * (Ad3.uni2 x * Ad3.dg2 b₁ b₂ * κ) =
      Ad3.uni2 ((t₁ : F) * x * ((t₂⁻¹ : Fˣ) : F)) * (Ad3.dg2 (t₂ * b₂) (t₂ * b₂) *
        (Ad3.dg2 (t₁ * b₁ * (t₂ * b₂)⁻¹) 1 * κ)) := by
    rw [← mul_assoc (Ad3.dg2 (t₂ * b₂) (t₂ * b₂)), ← GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_diagonal_alt, ← mul_assoc, ← mul_assoc,
      ← mul_assoc, GlobalTheory.CompanionTheory.WhittakerIwasawa.diagonal_mul_unipotent]
    simp only [mul_assoc]
  rw [e', hu, hd, norm_mul, Circle.norm_coe, one_mul]
  exact hb _ κ hκ

lemma shell_exponent_identity (q A e : ℝ) (L m n : ℤ) (hq : 1 < q) :
    A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n)
      = A * q ^ L * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ))) := by
  have hq0 : 0 < q := by linarith
  have e1 : q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (((L - n : ℤ)) : ℝ)
      = q ^ (L : ℝ) * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ))) := by
    rw [← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1
    push_cast
    ring
  rw [Real.rpow_intCast, Real.rpow_intCast] at e1
  linear_combination A * e1

theorem lintegral_le_of_shells (e : ℝ) :
    ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) (q A τ : ℝ) (L : ℤ) (c T₁ T₂ : ℝ≥0∞)
      (S : ℤ → ℤ → Set X) (Φ : X → ℝ≥0∞), 1 < q → 0 ≤ A → 0 < τ →
      (∀ m n, MeasurableSet (S m n)) →
      (∀ m n, n ≤ L → μ (S m n) ≤ ENNReal.ofReal (q ^ (L - n)) * c) →
      (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0)) ≤ T₁ →
      (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0)) ≤ T₂ →
      (∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
        Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2))) →
      ∫⁻ y, Φ y ∂μ ≤ ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by
  intro X _ μ q A τ L c T₁ T₂ S Φ hq hA hτ hS hμ hT1 hT2 hΦ
  have hq0 : 0 < q := by linarith
  let a : ℤ → ℝ≥0∞ := fun m => if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0
  let b : ℤ → ℝ≥0∞ := fun n =>
    if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0
  let w : ℤ × ℤ → ℝ≥0∞ := fun p =>
    if p.1 ≤ L ∧ p.2 ≤ L ∧ τ * q ^ (-p.2) ≤ q ^ L then
      ENNReal.ofReal (A * q ^ (((p.2 : ℝ) - p.1) * e) * q ^ (((p.1 : ℝ) + p.2) / 2))
    else 0
  have hpt : ∀ y, Φ y ≤ ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y := by
    intro y
    by_cases h0 : Φ y = 0
    · simp [h0]
    obtain ⟨m, n, h1, h2, h3, h4, h5⟩ := hΦ y h0
    refine le_trans ?_ (ENNReal.le_tsum (m, n))
    have hw : w (m, n) = ENNReal.ofReal
        (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
      simp only [w]
      rw [if_pos ⟨h1, h2, h3⟩]
    rw [Set.indicator_of_mem (show y ∈ S (m, n).1 (m, n).2 from h4), hw]
    exact h5
  have hterm : ∀ p : ℤ × ℤ,
      w p * μ (S p.1 p.2) ≤ ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) := by
    rintro ⟨m, n⟩
    by_cases hc : m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L
    · obtain ⟨h1, h2, h3⟩ := hc
      have hw : w (m, n) = ENNReal.ofReal
          (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
        simp only [w]
        rw [if_pos ⟨h1, h2, h3⟩]
      have ha : a m = ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) := by
        simp only [a]
        rw [if_pos h1]
      have hb : b n = ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) := by
        simp only [b]
        rw [if_pos h3]
      have hnn1 : 0 ≤ A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) := by positivity
      have hnn2 : 0 ≤ A * q ^ L := by positivity
      have hnn3 : 0 ≤ q ^ ((1 / 2 - e) * (m : ℝ)) := by positivity
      show w (m, n) * μ (S m n) ≤ ENNReal.ofReal (A * q ^ L) * (a m * b n * c)
      rw [hw, ha, hb]
      calc ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) * μ (S m n)
          ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) *
              (ENNReal.ofReal (q ^ (L - n)) * c) := by
            gcongr
            exact hμ m n h2
        _ = ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2) * q ^ (L - n))
              * c := by
            rw [ENNReal.ofReal_mul hnn1]
            ring
        _ = ENNReal.ofReal (A * q ^ L * q ^ ((1 / 2 - e) * (m : ℝ)) * q ^ ((1 / 2 - e) * (-(n : ℝ)))) * c := by
            rw [shell_exponent_identity q A e L m n hq]
        _ = ENNReal.ofReal (A * q ^ L) *
              (ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) * ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) * c) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hnn2]
            ring
    · have hw : w (m, n) = 0 := by
        simp only [w]
        rw [if_neg hc]
      show w (m, n) * μ (S m n) ≤ _
      rw [hw, zero_mul]
      exact zero_le
  have hfac : ∑' p : ℤ × ℤ, a p.1 * b p.2 * c = (∑' m, a m) * (∑' n, b n) * c := by
    rw [ENNReal.tsum_prod (f := fun m n => a m * b n * c)]
    simp only [mul_assoc]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  calc ∫⁻ y, Φ y ∂μ
      ≤ ∫⁻ y, ∑' p : ℤ × ℤ, (S p.1 p.2).indicator (fun _ => w p) y ∂μ := lintegral_mono hpt
    _ = ∑' p : ℤ × ℤ, ∫⁻ y, (S p.1 p.2).indicator (fun _ => w p) y ∂μ :=
        lintegral_tsum fun p => (measurable_const.indicator (hS p.1 p.2)).aemeasurable
    _ = ∑' p : ℤ × ℤ, w p * μ (S p.1 p.2) := by
        refine tsum_congr fun p => ?_
        exact lintegral_indicator_const (hS p.1 p.2) (w p)
    _ ≤ ∑' p : ℤ × ℤ, ENNReal.ofReal (A * q ^ L) * (a p.1 * b p.2 * c) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (A * q ^ L) * ((∑' m, a m) * (∑' n, b n) * c) := by
        rw [ENNReal.tsum_mul_left, hfac]
    _ ≤ ENNReal.ofReal (A * q ^ L) * (T₁ * T₂ * c) := by
        gcongr
    _ = ENNReal.ofReal (A * q ^ L) * T₁ * T₂ * c := by ring

open Ad3 Ad3.LFS in

theorem gInt2 (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (V' : Submodule ℂ (GL (Fin 2) F → ℂ)), WhittakerModelGL2 ψ ν ν⁻¹ V' → ∀ W' ∈ V',
    ∀ R : ℝ, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      Integrable ((om R t₂).indicator fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ))
        (hG ψ) ∧
      ∫ k, (om R t₂).indicator (fun k => ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)) k ∂hG ψ ≤
        C * (modulus (t₁ : F) : ℝ) ^ e * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ) := by
  intro F _ _ _ _ _ _ ψ ν V' H W' hW' R
  classical
  have hδ : 0 < 1 / 2 - e := by linarith
  obtain ⟨C, B, hCB⟩ := H.bound W' hW' (1 / 2 - e) hδ
  set q : ℝ := (residueCard F : ℝ) with hqdef
  have hq : 1 < q := by rw [hqdef]; exact_mod_cast (one_lt_residueCard (K := F))
  have hq0 : 0 < q := by linarith
  obtain ⟨L₀, hL₀⟩ := pow_unbounded_of_one_lt R hq
  set L : ℤ := (L₀ : ℤ) with hLdef
  have hRL : R ≤ q ^ L := by rw [hLdef, zpow_natCast]; exact hL₀.le
  haveI hμ : (hG ψ).IsHaarMeasure := by unfold hG; infer_instance
  haveI hinv : (hG ψ).IsInvInvariant := ⟨Measures.inv_eq_self_GL F 2 (hG ψ)⟩
  set Kμ : ℝ≥0∞ := hG ψ (GLnLocal.integralGL F 2 : Set (GL (Fin 2) F)) with hKμ
  have hKfin : Kμ ≠ ∞ := (GLnLocal.isCompact_integralGL F 2).measure_lt_top.ne
  set C₁ : ℝ := max C 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  have hbound : ∀ (a : Fˣ), ∀ κ ∈ GLnLocal.integralGL F 2,
      ‖W' (dg2 a 1 * κ)‖ ≤ C₁ * (modulus (a : F) : ℝ) ^ e := by
    intro a κ hκ
    have h := (hCB a κ hκ).1
    rw [show (1 / 2 - (1 / 2 - e) : ℝ) = e by ring] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hpsi : ∀ x g, W' (uni2 x * g) = (ψ x : ℂ) * W' g := H.psi W' hW'
  have hcen : ∀ (a : Fˣ) g, W' (dg2 a a * g) = W' g := by
    intro a g
    rw [H.cen W' hW']
    simp
  obtain ⟨U, hU⟩ := H.smooth W' hW'
  have hWc : Continuous W' := by
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  have hval : Continuous fun k : GL (Fin 2) F => (k : Matrix (Fin 2) (Fin 2) F) := Units.continuous_val
  have hmod : Continuous fun x : F => (modulus x : ℝ) := NNReal.continuous_coe.comp continuous_modulus
  have hdet : Continuous fun k : GL (Fin 2) F => (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) := by
    have : Continuous fun k : GL (Fin 2) F => ((GeneralLinearGroup.det k : Fˣ) : F) := by
      simpa using hval.matrix_det
    exact hmod.comp this
  have homc : ∀ t : Fˣ, IsClosed (om R t : Set (GL (Fin 2) F)) := by
    intro t
    have e : (om R t : Set (GL (Fin 2) F)) = (⋂ i, ⋂ j, {k : GL (Fin 2) F | (modulus ((k : Matrix (Fin 2) (Fin 2) F) i j) : ℝ) ≤ R}) ∩
        ⋂ j, {k : GL (Fin 2) F | (modulus ((t : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) : ℝ) ≤ R} := by
      ext k
      simp [om]
    rw [e]
    refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (hmod.comp (hval.matrix_elem i j)) continuous_const) (isClosed_iInter fun j =>
      isClosed_le (hmod.comp (continuous_const.mul ((hval.comp continuous_inv).matrix_elem 1 j))) continuous_const)
  set r : ℝ := q ^ (-(1 / 2 - e) : ℝ) with hr
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  set D : ℝ := 1 - r with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hqL : 0 < q ^ L := zpow_pos hq0 L
  refine ⟨C₁ * q ^ L * ((q ^ L) ^ (1 / 2 - e) / D) ^ 2 * Kμ.toReal, fun t₁ t₂ => ?_⟩
  set τ : ℝ := (modulus (t₂ : F) : ℝ) with hτdef
  have hτ : 0 < τ := by exact_mod_cast modulus_pos t₂.ne_zero
  set σ : ℝ := (modulus (t₁ : F) : ℝ) with hσdef
  have hσ : 0 < σ := by exact_mod_cast modulus_pos t₁.ne_zero
  set f : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => Set.indicator_nonneg (fun _ _ => by positivity) k
  have hfm : Measurable f := by
    refine Measurable.indicator (Continuous.measurable ?_) (homc t₂).measurableSet
    exact (hWc.comp (continuous_const.mul continuous_inv)).norm.mul
      (hdet.rpow_const fun _ => Or.inr (by norm_num))
  set A : ℝ := C₁ * (σ / τ) ^ e with hA
  have hA0 : 0 ≤ A := by positivity
  set T₁r : ℝ := (q ^ L) ^ (1 / 2 - e) / D with hT₁r
  set T₂r : ℝ := (q ^ L / τ) ^ (1 / 2 - e) / D with hT₂r
  have hT₁ : (∑' m : ℤ, (if m ≤ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (m : ℝ))) else 0)) ≤ ENNReal.ofReal T₁r := by
    have h := GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div q (1 / 2 - e) (q ^ L) hq hδ hqL
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [zpow_le_zpow_iff_right₀ hq]
  have hT₂ : (∑' n : ℤ, (if τ * q ^ (-n) ≤ q ^ L then ENNReal.ofReal (q ^ ((1 / 2 - e) * (-(n : ℝ)))) else 0)) ≤ ENNReal.ofReal T₂r := by
    have h := GlobalTheory.CompanionTheory.GeomSum.tsum_zpow_le_rpow_div q (1 / 2 - e) (q ^ L / τ) hq hδ (div_pos hqL hτ)
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine le_of_eq_of_le (tsum_congr fun m => ?_) h
    simp only [Equiv.neg_apply, neg_neg, Int.cast_neg]
    have e : τ * q ^ m ≤ q ^ L ↔ q ^ m ≤ q ^ L / τ := by rw [le_div_iff₀ hτ, mul_comm]
    simp only [e]
  set S : ℤ → ℤ → Set (GL (Fin 2) F) := fun m n => {g : GL (Fin 2) F | ∃ x : F, (modulus x : ℝ) ≤ q ^ (L - m) ∧
    ∃ κ ∈ GLnLocal.integralGL F 2, g = uni2 x * dg2 (unifUnit F ^ m) (unifUnit F ^ n) * κ} with hS
  set Φ : GL (Fin 2) F → ℝ≥0∞ := fun g => ENNReal.ofReal (f g⁻¹) with hΦ
  have hcov : ∀ y, Φ y ≠ 0 → ∃ m n : ℤ, m ≤ L ∧ n ≤ L ∧ τ * q ^ (-n) ≤ q ^ L ∧ y ∈ S m n ∧
      Φ y ≤ ENNReal.ofReal (A * q ^ (((n : ℝ) - m) * e) * q ^ (((m : ℝ) + n) / 2)) := by
    intro g hg
    have hom : g⁻¹ ∈ om R t₂ := by
      by_contra h
      exact hg (by simp [hΦ, hf, h])
    obtain ⟨x, m, n, κ, hκ, rfl⟩ := GlobalTheory.CompanionTheory.GIntIw.iwasawa_decomposition_gl_two F g
    obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.CompanionTheory.LFCoords.coords F x m n L κ R t₂ hκ hRL hom
    refine ⟨m, n, h1, h2, h4, ⟨x, h3, κ, hκ, rfl⟩, ENNReal.ofReal_le_ofReal ?_⟩
    rw [hf, Set.indicator_of_mem hom, inv_inv]
    have hw := whittaker_bound_iwasawa e F ψ W' C₁ hpsi hcen hbound t₁ t₂ (unifUnit F ^ m) (unifUnit F ^ n) x κ hκ
    have hu : ∀ k : ℤ, (modulus (((unifUnit F ^ k : Fˣ)) : F) : ℝ) = q ^ (-(k : ℝ)) := by
      intro k
      rw [modulus_of_ne_zero (Units.ne_zero _), ord_unifUnit_zpow, NNReal.coe_zpow, NNReal.coe_natCast,
        ← Real.rpow_intCast]
      push_cast
      rfl
    have hM : (modulus ((t₁ * unifUnit F ^ m * (t₂ * unifUnit F ^ n)⁻¹ : Fˣ) : F) : ℝ) =
        (σ / τ) * q ^ ((n : ℝ) - m) := by
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, modulus_mul, modulus_mul,
        modulus_inv, modulus_mul]
      simp only [NNReal.coe_mul, NNReal.coe_inv]
      rw [hu, hu, ← hσdef, ← hτdef, sub_eq_add_neg, Real.rpow_add hq0, Real.rpow_neg hq0.le (m : ℝ),
        Real.rpow_neg hq0.le (n : ℝ)]
      have := (Real.rpow_pos_of_pos hq0 (m : ℝ)).ne'
      have := (Real.rpow_pos_of_pos hq0 (n : ℝ)).ne'
      field_simp
    have hdetg := GlobalTheory.CompanionTheory.LFGInt2.modulus_det_iwasawa_inv F x (unifUnit F ^ m) (unifUnit F ^ n) κ hκ
    rw [hM] at hw
    rw [hdetg, hu, hu, mul_inv, ← Real.rpow_neg hq0.le, ← Real.rpow_neg hq0.le, neg_neg, neg_neg,
      ← Real.rpow_add hq0, ← Real.rpow_mul hq0.le]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hq0.le] at hw
    have e2 : ((m : ℝ) + n) * (1 / 2) = ((m : ℝ) + n) / 2 := by ring
    rw [e2, hA, mul_assoc C₁]
    exact mul_le_mul_of_nonneg_right hw (by positivity)
  have hmain := lintegral_le_of_shells e (hG ψ) q A τ L Kμ _ _ S Φ hq hA0 hτ
    (fun m n => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).1.measurableSet)
    (fun m n hn => (GlobalTheory.CompanionTheory.IwasawaShell.shell_open_volume F (hG ψ) m n L).2 hn)
    hT₁ hT₂ hcov
  have hinvl : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ = ∫⁻ g, Φ g ∂hG ψ :=
    ((Measure.measurePreserving_inv (hG ψ)).lintegral_comp hfm.ennreal_ofReal).symm
  set Rr : ℝ := C₁ * q ^ L * ((q ^ L) ^ (1 / 2 - e) / D) ^ 2 * Kμ.toReal * σ ^ e * τ ^ (-(1 / 2) : ℝ) with hRr
  have hRr0 : 0 ≤ Rr := by positivity
  have hfin : ∫⁻ k, ENNReal.ofReal (f k) ∂hG ψ ≤ ENNReal.ofReal Rr := by
    rw [hinvl]
    refine hmain.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_toReal hKfin, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hw0 : 0 < τ ^ e := Real.rpow_pos_of_pos hτ _
    have hw1 : 0 < τ ^ (1 / 2 - e) := Real.rpow_pos_of_pos hτ _
    have hw2 : τ ^ (-(1 / 2) : ℝ) = (τ ^ e * τ ^ (1 / 2 - e))⁻¹ := by
      rw [← Real.rpow_add hτ, ← Real.rpow_neg hτ.le]
      congr 1
      ring
    rw [hRr, hA, hT₁r, hT₂r, hw2, Real.div_rpow hσ.le hτ.le, Real.div_rpow hqL.le hτ.le]
    field_simp
  refine ⟨⟨hfm.aestronglyMeasurable, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hfm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hRr0 hfin

theorem rpow_torus (e : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a * b) ^ (1 / 2 : ℝ) * (a ^ e * b ^ (-(1 / 2) : ℝ)) = a ^ (1 / 2 + e) := by
  rw [Real.mul_rpow ha.le hb.le, Real.rpow_neg hb.le, Real.rpow_add ha]
  have hb' : b ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hb _).ne'
  field_simp

open Ad3 Ad3.LFS in

theorem gTor (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ‖Wp ψ W' Φ (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hyp
  obtain ⟨hs, hu, ⟨V', hV, hW⟩, hΦ⟩ := id hyp
  obtain ⟨C₁, R, h1⟩ := GlobalTheory.CompanionTheory.LFFour.gFour F ψ hs Φ hΦ
  obtain ⟨C₂, h2⟩ := gInt2 e he0 he1 F ψ ν V' hV W' hW R
  refine ⟨max C₁ 0 * max C₂ 0, fun t₁ t₂ => ?_⟩
  obtain ⟨hint, hle⟩ := h2 t₁ t₂
  have hm1 : 0 < (modulus (t₁ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₁.ne_zero
  have hm2 : 0 < (modulus (t₂ : F) : ℝ) := by
    exact_mod_cast GroundTheory.LocalField.modulus_pos t₂.ne_zero
  have hC₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂ : 0 ≤ max C₂ 0 := le_max_right _ _
  set G : GL (Fin 2) F → ℝ := (om R t₂).indicator fun k =>
    ‖W' (dg2 t₁ t₂ * k⁻¹)‖ * (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ)
    with hGd
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) k
  have hpt : ∀ k : GL (Fin 2) F,
      ‖W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)‖ ≤
        max C₁ 0 * G k := by
    intro k
    by_cases hp : pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) = 0
    · rw [hp, mul_zero, norm_zero]
      exact mul_nonneg hC₁ (hG0 k)
    · obtain ⟨hb, hsup⟩ := h1 (k : Matrix (Fin 2) (Fin 2) F)
        (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j)
      obtain ⟨hk, hξ⟩ := hsup hp
      have hmem : k ∈ om R t₂ := ⟨hk, hξ⟩
      have hGk : G k = ‖W' (dg2 t₁ t₂ * k⁻¹)‖ *
          (modulus ((GeneralLinearGroup.det k : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) := by
        rw [hGd, Set.indicator_of_mem hmem]
      rw [norm_mul, norm_mul, GlobalTheory.CompanionTheory.LFTor.norm_mp_half, ← hGk, mul_comm]
      exact mul_le_mul ((hb).trans (le_max_left _ _)) le_rfl
        (by rw [hGk]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)) hC₁
  have hbound : ‖∫ k, W' (dg2 t₁ t₂ * k⁻¹) * mp (GeneralLinearGroup.det k) (1 / 2) *
        pft ψ Φ (k : Matrix (Fin 2) (Fin 2) F)
          (fun j => (t₂ : F) * ((k⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 j) ∂hG ψ‖ ≤
      max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ e *
        (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := integral_mono_of_nonneg (μ := hG ψ)
      (Filter.Eventually.of_forall fun k => norm_nonneg _)
      (hint.const_mul (max C₁ 0)) (Filter.Eventually.of_forall hpt)
    refine hmono.trans ?_
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hC₁
    refine hle.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (mul_nonneg (Real.rpow_nonneg hm1.le _) (Real.rpow_nonneg hm2.le _))
  rw [GlobalTheory.CompanionTheory.LFGTorus.gtorus F ψ ν W' Φ hyp t₁ t₂, norm_mul, GlobalTheory.CompanionTheory.LFTor.norm_mp_half, Units.val_mul, GroundTheory.LocalField.modulus_mul,
    NNReal.coe_mul]
  calc _ ≤ ((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
        (max C₁ 0 * (max C₂ 0 * ((modulus (t₁ : F) : ℝ) ^ e *
          (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) _)
    _ = max C₁ 0 * max C₂ 0 * (((modulus (t₁ : F) : ℝ) * modulus (t₂ : F)) ^ (1 / 2 : ℝ) *
          ((modulus (t₁ : F) : ℝ) ^ e * (modulus (t₂ : F) : ℝ) ^ (-(1 / 2) : ℝ))) := by ring
    _ = _ := by rw [rpow_torus e hm1 hm2]

open Ad3 Ad3.LFS in
open scoped Pointwise in

theorem gK (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F]
    [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) W' Φ, Hyp ψ ν W' Φ →
    ∃ C : ℝ, ∀ t₁ t₂ : Fˣ, ∀ k ∈ GLnLocal.integralGL F 3,
      ‖Wp ψ W' Φ (dg t₁ t₂ 1 * k)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hH
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFSmooth.smoothW F ψ ν W' Φ hH
  have hT := GlobalTheory.CompanionTheory.LFTrans.sTrans
  have hcov : ((GLnLocal.integralGL F 3 : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F)) ⊆
      ⋃ k : GL (Fin 3) F, k • (U : Set (GL (Fin 3) F)) := by
    intro k _
    exact Set.mem_iUnion.2 ⟨k, 1, U.one_mem, by simp⟩
  obtain ⟨t, ht⟩ := (GLnLocal.isCompact_integralGL F 3).elim_finite_subcover
    (fun k : GL (Fin 3) F => k • (U : Set (GL (Fin 3) F))) (fun k => U.isOpen.smul k) hcov
  have hC : ∀ k : GL (Fin 3) F, ∃ C : ℝ, ∀ t₁ t₂ : Fˣ,
      ‖Wp ψ W' (rtr k Φ) (dg t₁ t₂ 1)‖ ≤ C * (modulus (t₁ : F) : ℝ) ^ (1 / 2 + e) := fun k =>
    gTor e he0 he1 F ψ ν W' (rtr k Φ) ⟨hH.1, hH.2.1, hH.2.2.1, (hT F ψ W' Φ k hH.2.2.2).1⟩
  choose C hC using hC
  refine ⟨∑ k ∈ t, max (C k) 0, fun a b k hk => ?_⟩
  obtain ⟨ki, hki, hmem⟩ := Set.mem_iUnion₂.1 (ht hk)
  obtain ⟨u, hu, rfl⟩ := hmem
  have hW : Wp ψ W' Φ (dg a b 1 * (ki • u)) = Wp ψ W' (rtr ki Φ) (dg a b 1) := by
    rw [smul_eq_mul, ← mul_assoc, hU _ u hu]
    exact congrFun (hT F ψ W' Φ ki hH.2.2.2).2 _
  have hnn : 0 ≤ (modulus (a : F) : ℝ) ^ (1 / 2 + e) := by positivity
  have hle : C ki ≤ ∑ k ∈ t, max (C k) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun k => max (C k) 0)
      (fun _ _ => le_max_right _ _) hki)
  rw [hW]
  exact (hC ki a b).trans (mul_le_mul_of_nonneg_right hle hnn)

theorem dg_eq_central {F : Type} [Field F] (t₁ t₂ t₃ : Fˣ) :
    Ad3.dg t₁ t₂ t₃ = Ad3.dg t₃ t₃ t₃ * Ad3.dg (t₁ / t₃) (t₂ / t₃) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals field_simp

end GlobalTheory.CompanionTheory.LFTempered

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol

namespace GlobalTheory.CompanionTheory.LFTempered

theorem temperedBoundGL3_of_lift : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (ν : Fˣ →* ℂˣ) (W' : GL (Fin 2) F → ℂ) (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), LFS.Hyp ψ ν W' Φ → TemperedBoundGL3 (LFS.Wp ψ W' Φ) := by
  intro F _ _ _ _ _ _ ψ ν W' Φ hH
  obtain ⟨U, hU⟩ := GlobalTheory.CompanionTheory.LFSmooth.smoothW F ψ ν W' Φ hH
  refine ⟨?_, fun ε h0 h1 => ?_⟩
  · refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    refine ⟨{x | g⁻¹ * x ∈ U}, U.isOpen.preimage (continuous_const.mul continuous_id), by simp [U.one_mem],
      fun x hx => ?_⟩
    have := hU g _ hx
    simpa using this
  · obtain ⟨C, hC⟩ := gK (1 / 2 - ε) (by linarith) (by linarith) F ψ ν W' Φ hH
    obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.LFSupp.sSupp F ψ hH.1 (LFS.Wp ψ W' Φ)
      (GlobalTheory.CompanionTheory.LFPsi.sPsiW F ψ ν W' Φ hH) ⟨U, hU⟩
    refine ⟨C, B, fun t₁ t₂ t₃ k hk => ?_⟩
    have hcen : LFS.Wp ψ W' Φ (dg t₁ t₂ t₃ * k) = LFS.Wp ψ W' Φ (dg (t₁ / t₃) (t₂ / t₃) 1 * k) := by
      rw [dg_eq_central t₁ t₂ t₃, mul_assoc]
      exact GlobalTheory.CompanionTheory.LFCen.scenW F ψ ν W' Φ hH t₃ _
    rw [hcen]
    refine ⟨?_, fun hne => ?_⟩
    · have h := hC (t₁ / t₃) (t₂ / t₃) k hk
      rwa [show (1 / 2 + (1 / 2 - ε) : ℝ) = 1 - ε by ring] at h
    · have e1 : t₁ / t₂ * (t₂ / t₃) = t₁ / t₃ := div_mul_div_cancel _ _ _
      have := hB (t₁ / t₂) (t₂ / t₃) k hk (by rwa [e1])
      exact this

end GlobalTheory.CompanionTheory.LFTempered
