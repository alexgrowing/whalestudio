import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryOperatorCommutesSchrodinger

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.AdelicSchur

open GlobalTheory.AdelicSchur

theorem schur : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ M : Module.End ℂ ((κ → AF F) → ℂ), (∀ φ ∈ schA F κ, M φ ∈ schA F κ) →
    (∀ w : (κ → AF F) × (κ → AF F), ∀ φ ∈ schA F κ, M (schr ψ w φ) = schr ψ w (M φ)) →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖M φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    ∃ z : ℂ, ∀ φ ∈ schA F κ, M φ = z • φ := by
  intro F _ _ κ _ ψ hψ M hpres hcomm hiso
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  let μ : Measure (κ → AF F) := Measure.addHaar
  haveI hμH : μ.IsAddHaarMeasure := by dsimp [μ]; infer_instance
  have hL2 : ∀ φ ∈ schA F κ, MemLp φ 2 μ := fun φ hφ =>
    GlobalTheory.WeilM.schA_memLp_two F κ μ hμH φ hφ
  have hint : ∀ φ ∈ schA F κ, Integrable (fun x => ‖φ x‖ ^ 2) μ := fun φ hφ =>
    (hL2 φ hφ).integrable_norm_pow two_ne_zero
  have hnorm : ∀ φ ∈ schA F κ, ∫ x, ‖M φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := by
    intro φ hφ
    have h := hiso μ hμH φ hφ
    have e : ∀ g ∈ schA F κ, ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := fun g hg => by
      rw [ofReal_integral_eq_lintegral_ofReal (hint g hg) (Filter.Eventually.of_forall fun x => by positivity)]
      congr 1
      funext x
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rw [e _ (hpres φ hφ), e φ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hψn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.HeisLineTheta.norm_psi hψ
  have hcy : ∀ y : κ → AF F, Continuous fun x : κ → AF F => ψ (x ⬝ᵥ y) := fun y =>
    hψ.1.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const)
  have hschr0 : ∀ (y : κ → AF F) (f : (κ → AF F) → ℂ) x, schr ψ (0, y) f x = ψ (x ⬝ᵥ y) * f x := by
    intro y f x
    simp [schr]
  have hdiag : ∀ φ ∈ schA F κ, ∀ x, ‖M φ x‖ = ‖φ x‖ := by
    intro φ hφ
    have hMφ := hpres φ hφ
    set D : (κ → AF F) → ℝ := fun x => ‖M φ x‖ ^ 2 - ‖φ x‖ ^ 2 with hD
    have hDi : Integrable D μ := (hint _ hMφ).sub (hint φ hφ)
    have hDc : Continuous D :=
      ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hMφ).norm.pow 2).sub
        ((GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hφ).norm.pow 2)
    have hbi : ∀ (y : κ → AF F) (c : ℂ) (f : (κ → AF F) → ℂ), f ∈ schA F κ →
        Integrable (fun x => (c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) μ := fun y c f hf =>
      (hint f hf).bdd_mul (Complex.continuous_re.comp (continuous_const.mul (hcy y))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, hψn, mul_one])
    have hre : ∀ (y : κ → AF F) (c : ℂ), ∫ x, (c * ψ (x ⬝ᵥ y)).re * D x ∂μ = 0 := by
      intro y c
      have hg : φ + c • schr ψ (0, y) φ ∈ schA F κ :=
        (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ))
      have hMg : M (φ + c • schr ψ (0, y) φ) = M φ + c • schr ψ (0, y) (M φ) := by
        rw [map_add, map_smul, hcomm _ φ hφ]
      have h1 := hnorm _ hg
      rw [hMg] at h1
      have hpt : ∀ f : (κ → AF F) → ℂ, (fun x => ‖(f + c • schr ψ (0, y) f) x‖ ^ 2) =
          fun x => (1 + ‖c‖ ^ 2) * ‖f x‖ ^ 2 + 2 * ((c * ψ (x ⬝ᵥ y)).re * ‖f x‖ ^ 2) := by
        intro f
        funext x
        rw [Pi.add_apply, Pi.smul_apply, hschr0, smul_eq_mul,
          show f x + c * (ψ (x ⬝ᵥ y) * f x) = (1 + c * ψ (x ⬝ᵥ y)) * f x by ring, norm_mul, mul_pow,
          norm_one_add_sq c _ (hψn _)]
        ring
      rw [hpt, hpt, integral_add ((hint _ hMφ).const_mul _) ((hbi y c _ hMφ).const_mul _),
        integral_add ((hint _ hφ).const_mul _) ((hbi y c _ hφ).const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, hnorm φ hφ] at h1
      have h2 : ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 ∂μ = ∫ x, (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 ∂μ := by
        linarith
      have e : (fun x => (c * ψ (x ⬝ᵥ y)).re * D x) =
          fun x => (c * ψ (x ⬝ᵥ y)).re * ‖M φ x‖ ^ 2 - (c * ψ (x ⬝ᵥ y)).re * ‖φ x‖ ^ 2 := by
        funext x
        simp only [hD]
        ring
      rw [e, integral_sub (hbi y c _ hMφ) (hbi y c _ hφ), h2, sub_self]
    have hF : ∀ y : κ → AF F, ∫ x, ψ (x ⬝ᵥ y) * (D x : ℂ) ∂μ = 0 := by
      intro y
      have hI : Integrable (fun x => ψ (x ⬝ᵥ y) * (D x : ℂ)) μ :=
        hDi.ofReal.bdd_mul (hcy y).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (hψn _).le)
      apply Complex.ext
      · rw [Complex.zero_re, ← RCLike.re_to_complex, ← integral_re hI]
        have e : (fun x => RCLike.re (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((1 : ℂ) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re]
        rw [e]
        exact hre y 1
      · rw [Complex.zero_im, ← RCLike.im_to_complex, ← integral_im hI]
        have e : (fun x => RCLike.im (ψ (x ⬝ᵥ y) * (D x : ℂ))) = fun x => ((-Complex.I) * ψ (x ⬝ᵥ y)).re * D x := by
          funext x
          simp [Complex.mul_re, Complex.mul_im]
        rw [e]
        exact hre y (-Complex.I)
    have hD0 := GlobalTheory.CharFourierInj.real_eq_zero (G := κ → AF F) (A := κ → AF F) (fun y x => ψ (x ⬝ᵥ y)) hcy
      (fun y x x' => by simp only [add_dotProduct, AddChar.map_add_eq_mul])
      (fun y y' x => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
      (fun x => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
      (fun y x => hψn _) (fun x hx => GlobalTheory.AdelicSchur.sep ψ hψ x hx) μ D hDc hDi hF
    intro x
    have := congrFun hD0 x
    simp only [hD, Pi.zero_apply, sub_eq_zero] at this
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have htwo : ∀ φ ∈ schA F κ, ∀ φ' ∈ schA F κ, ∀ x a,
      star (M φ x) * M φ' (x + a) = star (φ x) * φ' (x + a) := by
    intro φ hφ φ' hφ' x a
    apply conj_mul_eq
    intro c
    have hg : φ + c • schr ψ (a, 0) φ' ∈ schA F κ :=
      (schA F κ).add_mem hφ ((schA F κ).smul_mem c (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'))
    have h1 := hdiag _ hg x
    rw [map_add, map_smul, hcomm _ φ' hφ'] at h1
    simpa [schr] using h1
  by_cases h0 : ∃ φ₀ ∈ schA F κ, ∃ x₀, φ₀ x₀ ≠ 0
  · obtain ⟨φ₀, hφ₀, x₀, hx₀⟩ := h0
    have hn1 : ‖M φ₀ x₀‖ = ‖φ₀ x₀‖ := hdiag φ₀ hφ₀ x₀
    have hs : star (M φ₀ x₀) ≠ 0 := by
      rw [star_ne_zero, ← norm_ne_zero_iff, hn1, norm_ne_zero_iff]
      exact hx₀
    refine ⟨star (φ₀ x₀) / star (M φ₀ x₀), fun φ hφ => funext fun x => ?_⟩
    have h2 := htwo φ₀ hφ₀ φ hφ x₀ (x - x₀)
    rw [add_sub_cancel] at h2
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs]
    exact (mul_comm _ _).trans h2
  · push_neg at h0
    refine ⟨0, fun φ hφ => ?_⟩
    have : φ = 0 := funext fun x => h0 φ hφ x
    rw [this, map_zero, smul_zero]

end GlobalTheory.HoweD.AdelicSchur
