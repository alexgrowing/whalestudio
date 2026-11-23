import Mathlib
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianLogNormLocalSumStatement
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem deg_eq_of_local_two_curves : ∀ (k E : Type) [Field k] [NumberField k] [Field E] [NumberField E] (τ : E →+* k) (N : LogNorms k) (ρ : k) (a r : E) (p q d : ℕ) (n n' : (k →+* ℂ) → ℝ) (x : ℝ) (t t' : Nat.Primes → E), ρ ≠ 0 → a ≠ 0 → 0 < d → r ^ 2 = -(d : E) → -(∑ s, Real.log (n s)) / Module.finrank ℚ k = x → -(∑ s, Real.log (n' s)) / Module.finrank ℚ k = x → (∀ s, N.inf s = Real.log ‖s ρ‖ + ((p : ℝ) / 2 * (Real.log (n s) + Real.log d / 2) - (q : ℝ) / 2 * (Real.log (n' s) + Real.log d / 2)) + Real.log ‖s (τ a)‖ / 2) → (∀ ℓ : Nat.Primes, ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t' ℓ)‖ = ∑ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖) → (∀ (ℓ : Nat.Primes) (j : E →+* ℂ_[ℓ]), Real.log ‖j (t ℓ)‖ + Real.log ‖j (t' ℓ)‖ + Real.log ‖j a‖ = -((p : ℝ) + q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) → {ℓ : Nat.Primes | ∃ j : E →+* ℂ_[ℓ], Real.log ‖j (t ℓ)‖ ≠ 0}.Finite → (∀ (ℓ : Nat.Primes) (j : k →+* ℂ_[ℓ]), N.fin ℓ j + q * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((d : ℕ) : ℂ_[ℓ])‖) = Real.log ‖j ρ‖ - Real.log ‖j (τ (t ℓ))‖ - q * logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((q : ℝ) - p) * (logIdeal ((j.comp τ).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (τ r)‖)) → N.IsAdelic ∧ N.deg = ((p : ℝ) - q) / 2 * (x - Real.log (rootDiscr E) + Real.log (Real.sqrt d)) + q * (2 * Real.log (Real.sqrt d) - Real.log (rootDiscr E)) := by
  intro k E _ _ _ _ τ N ρ a r p q d n n' x t t' hρ ha hd hr hn hn' hinf ht ht2 hfin hloc
  let N' : LogNorms k :=
    ⟨fun s => N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)), N.fin⟩
  have h := GlobalTheory.T.hermitian_log_norm_local_sum k E τ N' ρ a r p q d n x t t' hρ ha hd hr hn
    (fun s => by
      change N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s)) = _
      rw [hinf s]
      ring)
    ht ht2 hfin (fun ℓ j => hloc ℓ j)
  have hf : (Module.finrank ℚ k : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hs : ∑ s, Real.log (n' s) = ∑ s, Real.log (n s) := by
    have e := hn'.trans hn.symm
    rw [div_left_inj' hf] at e
    linarith
  have hsum : ∑ s, N'.inf s = ∑ s, N.inf s := by
    change ∑ s, (N.inf s + (q : ℝ) / 2 * (Real.log (n' s) - Real.log (n s))) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hs]
    simp
  have hdeg : N'.deg = N.deg := by
    unfold LogNorms.deg
    rw [hsum]
    rfl
  exact ⟨h.1, hdeg ▸ h.2⟩

end GlobalTheory.CompanionTheory.Ar.Fl
