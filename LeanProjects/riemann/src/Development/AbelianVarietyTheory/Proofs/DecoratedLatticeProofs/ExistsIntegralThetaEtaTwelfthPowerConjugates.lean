import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ClassMeanPeriods
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.EquidistributedConjugates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PeriodLatticeAgreement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPeriodElement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConjStatement
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IntegralXCore

theorem exists_integral_theta_ratio : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → ∀ (D : D7), Formalism.MainNotions.GL3Theta.admJ D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t → ∃ X : M, X ≠ 0 ∧ IsIntegral ℤ (X : ℂ) ∧ ∀ (ρ : M →ₐ[ℚ] ℂ) (ω₁ τ : ℂ), ω₁ ≠ 0 → 0 < τ.im → JacobiThetaHalfCharacteristic.IsPeriodLattice (lamConj M ρ (lamOf D cc δ)) ω₁ τ → ∀ a b : Fin 2, JacobiThetaHalfCharacteristic.IsEvenChar a b → JacobiThetaHalfCharacteristic.thetaChar a b (t ρ / ω₁) τ = 0 → ‖ρ X‖ = (‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ / ‖ModularForm.eta τ‖) ^ 12 := by
  intro hL hT D hJ cc δ M _ t hS
  obtain ⟨e, g, hg, hval, hρ⟩ := GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj D cc δ M t hS
  have crv : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hS.1, hS.2.1⟩
  have hYρ : ∀ ρ : M →ₐ[ℚ] ℂ, ρ ((12 * e ^ 2 - g) / 4) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) ^ 2 - g2 (lamConj M ρ (lamOf D cc δ))) / 4 := by
    intro ρ
    obtain ⟨-, h2, -, h4⟩ := hρ ρ
    rw [h2, h4]
    simp only [map_div₀, map_sub, map_mul, map_pow, map_ofNat]
  obtain ⟨d0, -, n0, -⟩ := hρ M.val
  have h20 := (hS.2.2.2 M.val).1
  have hY0 : (((12 * e ^ 2 - g) / 4 : M) : ℂ) =
      (12 * Formalism.MainNotions.StandardLatticesGL3.wpF (lamOf D cc δ) (t M.val) ^ 2 - g2 (lamOf D cc δ)) / 4 := by
    have h := hYρ M.val
    rw [hval] at h
    exact h
  rw [hval] at d0 n0 h20
  obtain ⟨L, hLL⟩ := (GlobalTheory.ThetaConj.isLat_lamOf crv).exists_periodPair
  obtain ⟨ω, τ, hω, hτ⟩ := GlobalTheory.exists_lattice_eq_mul_tau L
  have hP : JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D cc δ) ω (τ : ℂ) := fun x => by
    rw [hLL, hτ]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩
  obtain ⟨a, b, hab, hz⟩ := GlobalTheory.IntegralX.exists_char hω hP (hT τ).2.1 h20 n0
  obtain ⟨hne, s, hs, hX⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω τ _ hω hP d0 h20 n0 a b hab hz
  rw [← hY0] at hne hX
  have hYne : ((12 * e ^ 2 - g) / 4 : M) ≠ 0 := fun h => hne (by rw [h]; simp)
  refine ⟨1 / ((12 * e ^ 2 - g) / 4) ^ 3, one_div_ne_zero (pow_ne_zero _ hYne), ?_, ?_⟩
  · have e1 : ((1 / ((12 * e ^ 2 - g) / 4) ^ 3 : M) : ℂ) = 1 / (((12 * e ^ 2 - g) / 4 : M) : ℂ) ^ 3 := by
      push_cast
      rfl
    rw [e1, hX]
    exact GlobalTheory.IntegralX.integral hT _ ω τ hω hP d0 (hJ cc δ hS.1 hS.2.1) a b hab s hs
  · intro ρ ω₁ τ' hω₁ hτ' hP' a' b' hab' hz'
    obtain ⟨dρ, -, nρ, -⟩ := hρ ρ
    obtain ⟨-, s', hs', hX'⟩ := GlobalTheory.IntegralX.modulus hL hT _ ω₁ ⟨τ', hτ'⟩ (t ρ) hω₁ hP' dρ
      (hS.2.2.2 ρ).1 nρ a' b' hab' hz'
    rw [map_div₀, map_one, map_pow, hYρ, hX']
    have hs1 : ‖s'‖ = 1 := by rcases hs' with rfl | rfl <;> simp
    rw [norm_mul, hs1, one_mul, norm_pow, norm_div]

end GlobalTheory.IntegralXCore
