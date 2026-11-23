import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.FComb
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFinitePlaneMeasure
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Filter Topology
open scoped ValuativeRel
open Ad3 Ad3.LFS GlobalTheory.CompanionTheory.LFDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LFDual.ZRho

section Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem isCompact_modulus_le (R : ℝ) : IsCompact {x : F | (modulus x : ℝ) ≤ R} := by
  have hq : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hq
  have hO : IsCompact (𝒪[F] : Set F) := IsNonarchimedeanLocalField.isCompact_closedBall F 1
  set u : Fˣ := unifUnit F ^ (k : ℤ) with hu
  have hI : IsCompact ((fun y : F => y * ((u⁻¹ : Fˣ) : F)) '' (𝒪[F] : Set F)) :=
    hO.image (continuous_id.mul continuous_const)
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  refine hI.of_isClosed_subset (isClosed_le hmod continuous_const) ?_
  intro x hx
  refine ⟨x * (u : F), ?_, by simp⟩
  have hmu : (modulus (u : F) : ℝ) = ((residueCard F : ℝ) ^ k)⁻¹ := by
    rw [modulus_of_ne_zero u.ne_zero, hu, ord_unifUnit_zpow]
    push_cast
    rw [_root_.zpow_neg, zpow_natCast]
  have hx' : (modulus x : ℝ) ≤ R := hx
  have hpos : (0 : ℝ) < (residueCard F : ℝ) ^ k := by positivity
  apply (modulus_le_one_iff).1
  rw [modulus_mul, ← NNReal.coe_le_coe]
  push_cast
  rw [hmu, ← div_eq_mul_inv, div_le_one hpos]
  exact hx'.trans hk.le

theorem isCompact_shell {r : ℝ} (hr : 0 < r) (R : ℝ) :
    IsCompact {τ : Fˣ | r ≤ (modulus (τ : F) : ℝ) ∧ (modulus (τ : F) : ℝ) ≤ R} := by
  have hmod : Continuous fun x : F => (modulus x : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  have hK : IsCompact {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} :=
    (isCompact_modulus_le R).of_isClosed_subset
      ((isClosed_le continuous_const hmod).inter (isClosed_le hmod continuous_const))
      fun x hx => hx.2
  have hsub : {x : F | r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R} ⊆ Set.range (Units.val : Fˣ → F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      have := hx.1
      simp at this
      linarith
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact ((isOpenEmbedding_units_val (K := F)).isInducing.isCompact_preimage_iff hsub).2 hK

theorem continuous_mp (z : ℂ) : Continuous fun τ : Fˣ => mp τ z := by
  have hm : Continuous fun τ : Fˣ => (((modulus (τ : F) : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  exact hm.cpow continuous_const fun τ =>
    Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast modulus_pos τ.ne_zero)

end Compact

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem continuous_Atau {f : F → ℂ} {c : Fˣ →* ℂˣ} (hf : Continuous f) (hc : IsUnit1 c) (s lam : ℂ) :
    Continuous (Atau f c s lam) := by
  unfold Atau
  exact ((hf.comp Units.continuous_val).mul
    (Units.continuous_val.comp hc.1.inv)).mul (continuous_mp _)

theorem integrable_and_integral_Atau : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (f : F → ℂ) (c : Fˣ →* ℂˣ), Continuous f → (∃ r R : ℝ, 0 < r ∧ ∀ x, f x ≠ 0 → r ≤ (modulus x : ℝ) ∧ (modulus x : ℝ) ≤ R) → IsUnit1 c → ∀ s lam : ℂ, Integrable (Atau f c s lam) (rho F) ∧ ∫ τ, Atau f c s lam τ ∂rho F = kq F * localZeta f c⁻¹ (1 - s - lam) := by
  intro F _ _ _ _ _ _ f c hf ⟨r, R, hr, hsupp⟩ hc s lam
  have hmodc : Continuous fun τ : Fˣ => (modulus (τ : F) : ℝ) :=
    NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val)
  set k : ℝ := ((multHaarConst F).toReal)⁻¹ with hk
  have hk0 : 0 ≤ k := inv_nonneg.2 ENNReal.toReal_nonneg
  set g : Fˣ → ENNReal := fun τ => ENNReal.ofReal (k * (modulus (τ : F) : ℝ) ^ 2) with hg
  have hgm : Measurable g := (continuous_const.mul (hmodc.pow 2)).measurable.ennreal_ofReal
  have hglt : ∀ᵐ τ ∂multHaar F, g τ < ⊤ := Eventually.of_forall fun τ => ENNReal.ofReal_lt_top
  have hgr : ∀ τ, (g τ).toReal = k * (modulus (τ : F) : ℝ) ^ 2 := fun τ =>
    ENNReal.toReal_ofReal (by positivity)
  have hA := continuous_Atau hf hc s lam
  have hcont : Continuous fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ := by
    simp only [hgr]
    exact (continuous_const.mul (hmodc.pow 2)).smul hA
  have hcs : HasCompactSupport fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ := by
    refine HasCompactSupport.intro (isCompact_shell hr R) fun τ hτ => ?_
    have h0 : f (τ : F) = 0 := by
      by_contra h
      exact hτ (hsupp _ h)
    simp [Atau, h0]
  have hsm : Integrable (fun τ : Fˣ => (g τ).toReal • Atau f c s lam τ) (multHaar F) :=
    hcont.integrable_of_hasCompactSupport hcs
  refine ⟨(integrable_withDensity_iff_integrable_smul' hgm hglt).2 hsm, ?_⟩
  have hrho : rho F = (multHaar F).withDensity g := rfl
  rw [hrho, integral_withDensity_eq_integral_toReal_smul hgm hglt, localZeta, kq,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  have hm0 : (((modulus (τ : F) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero τ.ne_zero
  have hpow : (((modulus (τ : F) : ℝ)) : ℂ) ^ (1 - s - lam) =
      (((modulus (τ : F) : ℝ)) : ℂ) ^ 2 * mp τ (-s - 1 - lam) := by
    rw [mp, ← Complex.cpow_ofNat, ← Complex.cpow_add _ _ hm0]
    congr 1
    push_cast
    ring
  simp only [hgr, Atau, hpow, MonoidHom.inv_apply, Complex.real_smul]
  rw [hk]
  push_cast
  ring

end GlobalTheory.CompanionTheory.LFDual.ZRho
