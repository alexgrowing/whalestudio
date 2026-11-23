import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeOfMemChiGridBadPlaces

noncomputable section

namespace GlobalTheory.LamTie.AuxiliaryPrimeFunction

section General

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.GridChars GlobalTheory.CMVal

variable {L : Type} [Field L] [NumberField L]

theorem expAt_succ {χ : Formalism.L2.Host.HChar L} {v : HeightOneSpectrum (𝓞 L)} {n : ℕ} (h1 : χ.LevelLe v (n + 1))
    (h2 : ¬ χ.LevelLe v n) : ExpAt χ v (n + 1) := by
  have mono : ∀ a b : ℕ, a ≤ b → χ.LevelLe v a → χ.LevelLe v b := fun a b hab h x hx hx' =>
    h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))
  intro m
  refine ⟨fun h => ?_, fun h => mono _ _ h h1⟩
  by_contra hm
  exact h2 (mono _ _ (by omega) h)

theorem finite_over {p : ℕ} (hp : p.Prime) : {w : HeightOneSpectrum (𝓞 L) | (p : 𝓞 L) ∈ w.asIdeal}.Finite := by
  have h : Ideal.span {(p : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero
  refine (Ideal.finite_factors h).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 hw

theorem prime_eq {w : HeightOneSpectrum (𝓞 L)} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h1 : (p : 𝓞 L) ∈ w.asIdeal)
    (h2 : (q : 𝓞 L) ∈ w.asIdeal) : p = q := by
  by_contra hne
  have hc : IsCoprime (p : 𝓞 L) (q : 𝓞 L) := Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem natCast_mem_of_under {F : Type} [Field F] [NumberField F] [Algebra F L] {w w' : HeightOneSpectrum (𝓞 L)}
    (h : w.under (𝓞 F) = w'.under (𝓞 F)) {p : ℕ} (hp : (p : 𝓞 L) ∈ w.asIdeal) : (p : 𝓞 L) ∈ w'.asIdeal := by
  have key : ∀ u : HeightOneSpectrum (𝓞 L), (p : 𝓞 F) ∈ (u.under (𝓞 F)).asIdeal ↔ (p : 𝓞 L) ∈ u.asIdeal := fun u => by
    change algebraMap (𝓞 F) (𝓞 L) _ ∈ u.asIdeal ↔ _
    rw [map_natCast]
  exact (key w').1 (h ▸ (key w).2 hp)

end General

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

end GlobalTheory.LamTie.AuxiliaryPrimeFunction
