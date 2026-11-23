import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRepsTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealLatticeHasNonrealMultiplier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdeleTranslateIntegralAdditiveTotalPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeQuotientCorrespondenceOfTorsionTransporStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.NormSqOfSquareEqNeg

theorem normSq_of_sq_eq_neg (d : ℕ) (α : ℂ) (h : α ^ 2 = -(d : ℂ)) : (Complex.normSq α : ℂ) = d := by
  have h1 : Complex.normSq α ^ 2 = (d : ℝ) ^ 2 := by
    rw [← map_pow, h, Complex.normSq_neg, Complex.normSq_natCast]
    ring
  have h2 : Complex.normSq α = d := by
    have := Complex.normSq_nonneg α
    nlinarith [sq_nonneg (Complex.normSq α - d), sq_nonneg (Complex.normSq α + d), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  rw [h2]; simp

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ)
    (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), 0 < d → δ ^ 2 = -(d : K) → TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ →
    g (s2 Λ₀ / Ω₀ ^ 2) = s2 Λ₁ / Ω₁ ^ 2 := by
  intro K _ _ d δ ι g t Λ₀ Λ₁ Ω₀ Ω₁ hd hδ hT
  obtain ⟨_, _, _, hL₀, ⟨𝔞, _, hL₁⟩, _, _, hP⟩ := id hT
  obtain ⟨_, hm₀, him, hint⟩ := GlobalTheory.LatOfMult.main K d δ ι 1 Λ₀ hd hδ hL₀
  obtain ⟨_, hm₁, _, _⟩ := GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ₁ hd hδ hL₁
  have hα : ι δ ≠ 0 := fun h => him (by simp [h])
  have hδ0 : δ ≠ 0 := fun h => hα (by simp [h])
  have hα2 : ι δ ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ]; simp
  have hN : (Complex.normSq (ι δ) : ℂ) = d := normSq_of_sq_eq_neg d _ hα2
  have hc : ι δ ^ 2 - (Complex.normSq (ι δ) : ℂ) = -(2 * d : ℂ) := by rw [hα2, hN]; ring
  have hc0 : -(2 * d : ℂ) ≠ 0 := by
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    simpa using this
  obtain ⟨S, hS⟩ := kernel_reps_exist Λ₀ (ι δ) hα hm₀
  have hTr := GlobalTheory.T.isLatticeQuotientCorrespondence_of_torsionTransport K ι g t Λ₀ Λ₁ Ω₀ Ω₁ hT
  have hmul : ∀ x x', Tr t x x' → Tr t (δ * x) (δ * x') := fun x x' h => (GlobalTheory.T.isIdeleTranslateIntegral_additive_total_properties K t).2.1 δ x x' hint h
  obtain ⟨φ, S', hS', hbij, hrel⟩ := GlobalTheory.WpFam.kerReps_transport K ι Λ₀ Λ₁ (Tr t) δ S hTr hδ0 hmul hS
  have e₀ := quasiPeriodConstIsogeny_thm Λ₀ (ι δ) S hα hm₀ hS
  have e₁ := quasiPeriodConstIsogeny_thm Λ₁ (ι δ) S' hα hm₁ hS'
  rw [hc] at e₀ e₁
  have s₀ : s2 Λ₀ = (∑ P ∈ S, Λ₀.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₀]
  have s₁ : s2 Λ₁ = (∑ P ∈ S', Λ₁.weierstrassP P) / -(2 * d : ℂ) := by
    rw [eq_div_iff hc0, mul_comm, e₁]
  have key : ∀ P ∈ S, g (Λ₀.weierstrassP P / Ω₀ ^ 2) = Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 := by
    intro P hPS
    obtain ⟨k, k', hk, hk', hkk⟩ := hrel P hPS
    have hnot : ι k ∉ Λ₀.lattice := by rw [hk]; exact (hS.1 P hPS).2
    have := (hP k k' hnot hkk).1
    rwa [hk, hk'] at this
  have hsum : ∑ P ∈ S, Λ₁.weierstrassP (φ P) / Ω₁ ^ 2 = ∑ Q ∈ S', Λ₁.weierstrassP Q / Ω₁ ^ 2 :=
    Finset.sum_nbij φ (fun a ha => hbij.mapsTo ha) hbij.injOn hbij.surjOn (fun _ _ => rfl)
  have hg2 : g (-(2 * d : ℂ)) = -(2 * d : ℂ) := by simp [map_neg, map_mul, map_ofNat, map_natCast]
  rw [s₀, s₁, div_right_comm, div_right_comm (∑ P ∈ S', _), map_div₀, hg2, Finset.sum_div, Finset.sum_div, map_sum,
    Finset.sum_congr rfl key, hsum]

end GlobalTheory.NormSqOfSquareEqNeg
