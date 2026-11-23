import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEisensteinDivPeriod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularGroupRowVecAndConjRightActions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfLatticeTauLatticeMembership
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTauStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTransportSecondEisensteinCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMatrixOfConjugateTransportStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.Transp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ ω₀ ω₁ : ℂ, ω₀ = Ω₀ * c₀ / (2 * Real.pi * Complex.I) → ω₁ = Ω₁ * c₁ / (2 * Real.pi * Complex.I) → ω₀ ≠ 0 ∧ ω₁ ≠ 0 ∧ g (E₄ τ₀ / ω₀ ^ 4) = E₄ τ₁ / ω₁ ^ 4 ∧ g (E₆ τ₀ / ω₀ ^ 6) = E₆ τ₁ / ω₁ ^ 6 ∧ g (G2s τ₀ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₀ ^ 2) = G2s τ₁ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / ω₁ ^ 2 ∧ ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), (∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k') ∧ ∀ x, g (wp N x τ₀ / ω₀ ^ 2) = wp N (vmul x A) τ₁ / ω₁ ^ 2 ∧ g (wpd N x τ₀ / ω₀ ^ 3) = wpd N (vmul x A) τ₁ / ω₁ ^ 3 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT c₀ c₁ τ₀ τ₁ h₀ h₁ ω₀ ω₁ hω₀ hω₁
  subst hω₀ hω₁
  have hT' := hT
  obtain ⟨hΩ₀, hΩ₁, -, -, -, hg₂, hg₃, hwp⟩ := hT'
  have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have hE := map_eisenstein_div_period g Λ₀ Λ₁ c₀ c₁ Ω₀ Ω₁ τ₀ τ₁ h₀ h₁ hg₂ hg₃
  have hs₀ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₀ c₀ Ω₀ τ₀ h₀
  have hs₁ := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ₁ c₁ Ω₁ τ₁ h₁
  have hs := GlobalTheory.T.galois_transport_second_eisenstein_cm K d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  refine ⟨div_ne_zero (mul_ne_zero hΩ₀ h₀.1) h2πi, div_ne_zero (mul_ne_zero hΩ₁ h₁.1) h2πi,
    hE.1, hE.2, ?_, ?_⟩
  · rw [hs₀.1, hs₁.1, hs]
  · intro N _
    obtain ⟨A, hA⟩ := GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT c₀ c₁ τ₀ τ₁ h₀ h₁ N
    refine ⟨A, hA, fun x => ?_⟩
    rw [(hs₀.2 N x).1, (hs₀.2 N x).2, (hs₁.2 N (vmul x A)).1, (hs₁.2 N (vmul x A)).2]
    by_cases hx : x = 0
    · have hv : vmul x A = 0 := ((GlobalTheory.WpFam.Act.rightActions N).2.2.2.2.1 x A).2 hx
      have ht : ∀ τ : ℍ, tors N τ 0 = 0 := by intro τ; simp [tors]
      rw [hv, hx, ht, ht, mul_zero, mul_zero]
      simp [PeriodPair.weierstrassP_zero, PeriodPair.derivWeierstrassP_zero]
    · obtain ⟨k, k', hk, hk', htr⟩ := hA x
      have hnot : ι k ∉ Λ₀.lattice := by
        rw [hk, ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ₀ c₀ τ₀ h₀).1 _), ((GlobalTheory.WpFam.TorsMem.main N τ₀).2.2.1 x)]
        exact hx
      rw [← hk, ← hk']
      exact hwp k k' hnot htr

end GlobalTheory.WpFam.Transp
