import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_coprime_mul_le {A : Type} [CommRing A] [IsDedekindDomain A] (𝔞 J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (m : ℕ) (𝔟 : Ideal A), IsCoprime 𝔞 𝔟 ∧ 𝔞 ^ m * 𝔟 ≤ J := by
  classical
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hJ
  | h₂ u hu =>
    refine ⟨0, ⊤, Ideal.isCoprime_iff_sup_eq.mpr (sup_top_eq _), ?_⟩
    rw [Ideal.isUnit_iff.mp hu]; exact le_top
  | h₃ a p ha hp ih =>
    have ha0 : a ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    have hp0 : p ≠ ⊥ := by
      rintro rfl; exact hJ (by simp)
    obtain ⟨m, b, hcop, hle⟩ := ih ha0
    by_cases hap : 𝔞 ≤ p
    · refine ⟨m + 1, b, hcop, ?_⟩
      calc 𝔞 ^ (m + 1) * b = 𝔞 * (𝔞 ^ m * b) := by rw [pow_succ', _root_.mul_assoc]
        _ ≤ p * a := Ideal.mul_mono hap hle
    · have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp0
      have hc : IsCoprime 𝔞 p := by
        rw [Ideal.isCoprime_iff_sup_eq]
        by_contra h
        have h2 := hpm.eq_of_le h le_sup_right
        exact hap (h2 ▸ le_sup_left)
      refine ⟨m, p * b, IsCoprime.mul_right hc hcop, ?_⟩
      calc 𝔞 ^ m * (p * b) = p * (𝔞 ^ m * b) := by ring
        _ ≤ p * a := Ideal.mul_mono_right hle

theorem UpperTheory.Gal.crystallineComparison.Mod.idealSplit_of :
    IdealSplit := by
  intro A _ _ 𝔞 x hx ρ
  have hJ : Ideal.span {x} ≠ ⊥ := by simpa using hx
  obtain ⟨m, 𝔟, hc, hle⟩ := exists_coprime_mul_le 𝔞 (Ideal.span {x}) hJ
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp (hc.pow_left (m := ρ))
  refine ⟨m, j, ?_, fun a ha => hle (Ideal.mul_mem_mul ha hj)⟩
  have : j - 1 = -i := by rw [← hij]; ring
  rw [this]
  exact neg_mem hi
