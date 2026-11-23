import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerGaugeBound
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace F] [BorelSpace F] in

theorem continuous_of_rightInv {W : GL (Fin 2) F → ℂ} (U : OpenSubgroup (GL (Fin 2) F))
    (h : ∀ g, ∀ u ∈ U, W (g * u) = W g) : Continuous W := by
  refine IsLocallyConstant.continuous (IsLocallyConstant.iff_exists_open _ |>.2 fun g => ?_)
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' (U : Set (GL (Fin 2) F)),
    U.isOpen.preimage (continuous_const.mul continuous_id), by simp, fun x hx => ?_⟩
  have := h g _ hx
  simpa using this

def Good (ψ : AddChar F Circle) (W₀ : GL (Fin 2) F → ℂ) : Prop :=
  (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧
  (∃ U : OpenSubgroup (GL (Fin 2) F), ∀ g, ∀ u ∈ U, W₀ (g * u) = W₀ g) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
    ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
      (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B)

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_zero (ψ : AddChar F Circle) : Good ψ (0 : GL (Fin 2) F → ℂ) := by
  refine ⟨fun x g => by simp, fun a g => by simp, ⟨⊤, fun g u _ => by simp⟩,
    fun ε _ => ⟨0, 0, le_rfl, fun a k _ => ⟨by simp, fun h => absurd rfl h⟩⟩⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_add {ψ : AddChar F Circle} {W W' : GL (Fin 2) F → ℂ} (h : Good ψ W) (h' : Good ψ W') :
    Good ψ (W + W') := by
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := h
  obtain ⟨h1', h2', ⟨U', h3'⟩, h4'⟩ := h'
  refine ⟨fun x g => by simp [h1, h1', mul_add], fun a g => by simp [h2, h2'],
    ⟨U ⊓ U', fun g u hu => ?_⟩, fun ε hε => ?_⟩
  · have hu' : u ∈ U ∧ u ∈ U' := by simpa using hu
    simp [h3 g u hu'.1, h3' g u hu'.2]
  · obtain ⟨C, B, hC, hb⟩ := h4 ε hε
    obtain ⟨C', B', hC', hb'⟩ := h4' ε hε
    refine ⟨C + C', max B B', add_nonneg hC hC', fun a k hk => ⟨?_, fun hne => ?_⟩⟩
    · rw [add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hb a k hk).1 (hb' a k hk).1)
    · by_cases h0 : W (dg2 a 1 * k) = 0
      · have h0' : W' (dg2 a 1 * k) ≠ 0 := fun e => hne (by simp [h0, e])
        exact ((hb' a k hk).2 h0').trans (le_max_right _ _)
      · exact ((hb a k hk).2 h0).trans (le_max_left _ _)

omit [MeasurableSpace F] [BorelSpace F] in
theorem good_smul {ψ : AddChar F Circle} {W : GL (Fin 2) F → ℂ} (c : ℂ) (h : Good ψ W) :
    Good ψ (c • W) := by
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := h
  refine ⟨fun x g => by simp [h1]; ring, fun a g => by simp [h2],
    ⟨U, fun g u hu => by simp [h3 g u hu]⟩, fun ε hε => ?_⟩
  obtain ⟨C, B, hC, hb⟩ := h4 ε hε
  refine ⟨‖c‖ * C, B, mul_nonneg (norm_nonneg _) hC, fun a k hk => ⟨?_, fun hne => ?_⟩⟩
  · rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb a k hk).1 (norm_nonneg _)
  · exact (hb a k hk).2 fun e => hne (by simp [e])

theorem godement_whittaker_vector_good {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν : Fˣ →* ℂˣ} (hν : IsUnit1 ν)
    {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) :
    Good ψ (W2 ψ ν ν⁻¹ φ) := by
  have hν' : IsUnit1 ν⁻¹ := ⟨hν.1.inv, fun x => by simp [hν.2 x]⟩
  refine ⟨fun x g => GlobalTheory.CompanionTheory.WhittakerPsi.sPsi F ψ hψ ν ν⁻¹ hν hν' φ hφ x g, fun a g => ?_,
    GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth F ψ hψ ν ν⁻¹ hν hν' φ hφ, fun ε hε => ?_⟩
  · rw [GlobalTheory.CompanionTheory.WhittakerCentral.sCen F ψ hψ ν ν⁻¹ hν hν' φ hφ a g]
    simp
  · obtain ⟨C, B, hb⟩ := GlobalTheory.CompanionTheory.DampedWhittakerGauge.whittaker_torus_gauge_estimate F ψ hψ ν ν⁻¹ hν hν' φ hφ ε hε
    refine ⟨max C 0, B, le_max_right _ _, fun a k hk => ⟨?_, (hb a k hk).2⟩⟩
    exact (hb a k hk).1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem good_of_mem {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν : Fˣ →* ℂˣ} (hν : IsUnit1 ν)
    {W₀ : GL (Fin 2) F → ℂ} (hW : W₀ ∈ V2 ψ ν ν⁻¹) : Good ψ W₀ := by
  refine Submodule.span_induction ?_ (good_zero ψ) (fun _ _ _ _ h h' => good_add h h')
    (fun c _ _ h => good_smul c h) hW
  rintro _ ⟨φ, hφ, rfl⟩
  exact godement_whittaker_vector_good hψ hν hφ

theorem godement_vector_growth_support : ForS fun F _ _ _ _ _ _ ψ => ∀ ν : Fˣ →* ℂˣ, IsUnit1 ν → ∀ W₀ ∈ V2 ψ ν ν⁻¹,
    (∀ x g, W₀ (uni2 x * g) = (ψ x : ℂ) * W₀ g) ∧ (∀ (a : Fˣ) g, W₀ (dg2 a a * g) = W₀ g) ∧ Continuous W₀ ∧
    ∀ ε : ℝ, 0 < ε → ∃ C B : ℝ, 0 ≤ C ∧ ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W₀ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧ (W₀ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ ψ hψ ν hν W₀ hW
  obtain ⟨h1, h2, ⟨U, h3⟩, h4⟩ := good_of_mem hψ hν hW
  exact ⟨h1, h2, continuous_of_rightInv U h3, h4⟩

end GlobalTheory.CompanionTheory.GL2LocalData.GL2GodementVector
