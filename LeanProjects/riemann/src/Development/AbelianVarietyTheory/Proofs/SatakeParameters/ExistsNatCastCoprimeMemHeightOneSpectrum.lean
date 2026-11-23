import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormOneIdeleOrderOneTrivialElsewhere
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory

theorem natCast_mem_heightOneSpectrum_coprime :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  intro E _ _ p hp P hpP
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hmem : ∀ n : ℕ, ((n : 𝓞 E) ∈ P.asIdeal ↔ ringChar (𝓞 E ⧸ P.asIdeal) ∣ n) := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.spec _ n
  have hq0 : ringChar (𝓞 E ⧸ P.asIdeal) ≠ 0 := by
    intro h0
    have := (hmem _).1 (Ideal.absNorm_mem P.asIdeal)
    rw [h0, zero_dvd_iff] at this
    exact hN this
  have hqp : (ringChar (𝓞 E ⧸ P.asIdeal)).Prime :=
    (CharP.char_is_prime_or_zero (𝓞 E ⧸ P.asIdeal) _).resolve_right hq0
  refine ⟨ringChar (𝓞 E ⧸ P.asIdeal), hqp.pos, (hmem _).2 dvd_rfl, ?_⟩
  refine (Nat.coprime_primes hqp hp).2 ?_
  intro hq
  exact hpP ((hmem p).2 (hq ▸ dvd_rfl))

end GlobalTheory
