import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_coneTerm_neg_nat_rational :
    ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ), (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
  ∀ cs : List (Fin r), ∃ ρ : (Fin r → ℕ) → ℚ, ∀ m, DL cs (coneTerm a b (-(p : ℂ))) m = (ρ m : ℂ) := by
  intro ι _ r a b p h cs
  induction cs with
  | nil =>
    choose q hq using h
    refine ⟨q, fun m => ?_⟩
    show GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm a b (-(p : ℂ)) m = _
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm, neg_neg, Complex.cpow_natCast]
    rw [← Complex.ofReal_ratCast, ← hq m]
    simp only [Complex.ofReal_prod, Complex.ofReal_pow]
  | cons c cs ih =>
    obtain ⟨ρ, hρ⟩ := ih
    refine ⟨fun m => ρ (m + Pi.single c 1) - ρ m, fun m => ?_⟩
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at hρ ⊢
    rw [hρ, hρ, Rat.cast_sub]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
