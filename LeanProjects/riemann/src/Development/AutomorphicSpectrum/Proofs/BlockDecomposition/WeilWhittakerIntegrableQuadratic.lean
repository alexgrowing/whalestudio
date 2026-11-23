import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB.CaseZero

theorem real_bound {X Y a b δ M S P : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hδ : δ = a * b) (hbM : b ≤ M) (hP0 : 0 ≤ P) (hPS : P ≤ S) :
    (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * a)⁻¹ * P ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ * M * S * (X / Y) ^ (1 / 2 : ℝ) := by
  have hδ0 : 0 < δ := hδ ▸ mul_pos ha hb
  have hXY : 0 < X / Y := div_pos hX hY
  have e1 : (X * Y * δ) ^ (1 / 2 : ℝ) = (X / Y) ^ (1 / 2 : ℝ) * Y * δ ^ (1 / 2 : ℝ) := by
    have : X * Y * δ = (X / Y) * Y ^ 2 * δ := by field_simp
    rw [this, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hXY.le, Real.sqrt_sq hY.le]
  have e2 : a⁻¹ = b * δ⁻¹ := by rw [hδ]; field_simp
  have e3 : (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * a)⁻¹ * P
      = δ ^ (1 / 2 : ℝ) * δ⁻¹ * b * P * (X / Y) ^ (1 / 2 : ℝ) := by
    rw [e1, mul_inv, e2]
    field_simp
  rw [e3]
  have h1 : 0 ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ := by positivity
  have h2 : 0 ≤ (X / Y) ^ (1 / 2 : ℝ) := by positivity
  have h3 : b * P ≤ M * S := mul_le_mul hbM hPS hP0 (hb.le.trans hbM)
  calc δ ^ (1 / 2 : ℝ) * δ⁻¹ * b * P * (X / Y) ^ (1 / 2 : ℝ)
      = δ ^ (1 / 2 : ℝ) * δ⁻¹ * (b * P) * (X / Y) ^ (1 / 2 : ℝ) := by ring
    _ ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ * (M * S) * (X / Y) ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

theorem real_support {X Y a δ M T R : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hδ0 : 0 < δ)
    (haM : a ≤ M) (hT : T = ((Y * a) ^ 2)⁻¹ * (X * Y * δ)) (hTR : T ≤ R) :
    X / Y ≤ R * M ^ 2 / δ := by
  have e : X / Y = T * a ^ 2 / δ := by rw [hT]; field_simp
  rw [e]
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  gcongr
  exact hT0.trans hTR

theorem borel_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), IsUnit1 c → IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 = 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hc hΦ hcs h₀
  obtain ⟨M, hM, hMat⟩ := GlobalTheory.T.compact_translate_entries_bounded F h₀
  have hcont : Continuous Φ := hΦ.continuous
  obtain ⟨S, hS⟩ := hcs.exists_bound_of_continuous hcont
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hmodc : Continuous fun e : E => (modulus e : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  obtain ⟨R, hR⟩ := hcs.isCompact.bddAbove_image hmodc.continuousOn
  have hRΦ : ∀ e, Φ e ≠ 0 → (modulus e : ℝ) ≤ R := fun e he =>
    hR (Set.mem_image_of_mem _ (subset_tsupport _ he))
  set δ : ℝ := (modulus (h₀.val).det : ℝ) with hδdef
  have hdet0 : (h₀.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 h₀.isUnit
    exact this.ne_zero
  have hδ0 : 0 < δ := by
    simpa [hδdef] using modulus_pos hdet0
  refine ⟨δ ^ (1 / 2 : ℝ) * δ⁻¹ * M * S, max 1 (R * M ^ 2 / δ), by positivity,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x y k hk h10
  obtain ⟨hent, hdetm⟩ := hMat k hk
  set m : GL (Fin 2) F := k * h₀ with hm
  have hg : dg2 x y * k * h₀ = dg2 x y * m := by rw [hm, mul_assoc]
  rw [hg]
  set g : GL (Fin 2) F := dg2 x y * m with hgdef
  have hg10 : g.val 1 0 = 0 := by
    simp [hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two, h10]
  have hg11 : g.val 1 1 = (y : F) * m.val 1 1 := by
    simp [hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hgdet : (g.val).det = (x : F) * y * (m.val).det := by
    rw [hgdef, Units.val_mul, Matrix.det_mul]
    simp [dg2, Matrix.det_fin_two]
  have hmdet : (m.val).det = m.val 0 0 * m.val 1 1 := by
    simp [Matrix.det_fin_two, h10]
  have hmdet0 : (m.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
    exact this.ne_zero
  have h00 : m.val 0 0 ≠ 0 := fun h => hmdet0 (by rw [hmdet, h, zero_mul])
  have h11 : m.val 1 1 ≠ 0 := fun h => hmdet0 (by rw [hmdet, h, mul_zero])
  set X : ℝ := (modulus (x : F) : ℝ) with hXdef
  set Y : ℝ := (modulus (y : F) : ℝ) with hYdef
  set a : ℝ := (modulus (m.val 1 1) : ℝ) with hadef
  set b : ℝ := (modulus (m.val 0 0) : ℝ) with hbdef
  have hX : 0 < X := by simpa [hXdef] using modulus_pos x.ne_zero
  have hY : 0 < Y := by simpa [hYdef] using modulus_pos y.ne_zero
  have ha : 0 < a := by simpa [hadef] using modulus_pos h11
  have hb : 0 < b := by simpa [hbdef] using modulus_pos h00
  have hδab : δ = a * b := by
    rw [hδdef, ← hdetm, hmdet, modulus_mul, hadef, hbdef]
    push_cast
    ring
  have hxy : (modulus (((x / y : Fˣ)) : F) : ℝ) = X / Y := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    rw [hXdef, hYdef, div_eq_mul_inv]
  have hmg : (modulus (g.val).det : ℝ) = X * Y * δ := by
    rw [hgdet, modulus_mul, modulus_mul, hdetm]
    push_cast
    rfl
  have hm11 : (modulus (g.val 1 1) : ℝ) = Y * a := by
    rw [hg11, modulus_mul]
    push_cast
    rfl
  rw [hxy]
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0
  · refine ⟨?_, fun h => absurd hW h⟩
    rw [hW, norm_zero]
    positivity
  obtain ⟨t, htN, hval⟩ := GlobalTheory.T.weil_whittaker_galois_conjugate F E χ σ μ lam c Φ hc g hg10 hW
  refine ⟨?_, fun _ => ?_⟩
  · rw [hval, hmg, hm11]
    exact real_bound hX hY ha hb hδab (hent 0 0) (norm_nonneg _) (hS _)
  · have hΦτ : Φ (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) ≠ 0 := by
      intro h0
      apply hW
      have : ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = 0 := by rw [hval, h0]; simp
      exact norm_eq_zero.1 this
    have hT := hRΦ _ hΦτ
    have hmodτ : (modulus (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) : ℝ)
        = ((Y * a) ^ 2)⁻¹ * (X * Y * δ) := by
      rw [modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F) (E := E),
        ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E) (t : E), htN, modulus_inv]
      push_cast
      rw [hm11, hmg]
      field_simp
    exact (real_support hX hY ha hδ0 (hent 1 1) hmodτ hT).trans (le_max_right _ _)

end GlobalTheory.CompanionTheory.WcB.CaseZero
