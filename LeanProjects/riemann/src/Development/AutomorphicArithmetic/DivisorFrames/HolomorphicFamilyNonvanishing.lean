import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
import Development.AutomorphicArithmetic.DivisorFrames.ExistsComplexPointPrime
import Development.AutomorphicArithmetic.DivisorFrames.ExistsPrimeNonDivisible

theorem UpperTheory.holomorphic_family_nonvanishing :
    ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ) (m : ℕ) (ε : Fin m → ℂ), (∀ a : Fin m → K, ∑ j, σ (a j) * ε j = 0 → a = 0) → ∀ (a : A) (b : Fin m → A), a ≠ 0 → (∀ (d : ℕ) (B : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → (A →+* ℂ)), IsOpen B → (∀ z ∈ B, (φ z).comp (algebraMap K A) = σ) → (∀ u : A, DifferentiableOn ℂ (fun z => φ z u) B) → ∀ z₀ ∈ B, ∃ n : ℕ, n ≠ 0 ∧ ∃ M : ℝ, ∀ᶠ z in nhds z₀, ‖∑ j, ε j * φ z (b j)‖ ^ n ≤ M * ‖φ z a‖ ^ n) → ∀ j, a ∣ b j := by
  intro K A _ _ _ _ _ _ σ m ε hε a b ha H
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth K A
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  obtain ⟨P, t, c, j₀, hP, -, ht, hc0, h⟩ := UpperTheory.exists_prime_non_divisible A m b a ha (not_forall.1 hn)
  obtain ⟨ψ, hψσ, hψP, hψc⟩ := UpperTheory.exists_complex_point_prime K A σ m ε hε P hP c j₀ hc0
  obtain ⟨ι, -, d, B, φ, hB, hφσ, hd, hcov, hne⟩ := GlobalTheory.T.exists_countable_holomorphic_families_smooth K A σ
  obtain ⟨i, z₀, hz₀, hψ⟩ := hcov ψ hψσ
  obtain ⟨n, hn0, M, hM⟩ := H _ _ _ (hB i) (hφσ i) (hd i) z₀ hz₀
  have hc : ∀ u, ContinuousAt (fun z => φ i z u) z₀ := fun u =>
    (hd i u).continuousOn.continuousAt ((hB i).mem_nhds hz₀)
  have hcs : ContinuousAt (fun z => ∑ j, ε j * φ i z (c j)) z₀ :=
    tendsto_finset_sum _ fun j _ => (continuousAt_const.mul (hc (c j)))
  have hr0 : φ i z₀ t = 0 := by
    rw [hψ]
    exact hψP t ht
  have hs0 : ∑ j, ε j * φ i z₀ (c j) ≠ 0 := by rw [hψ]; exact hψc
  have hlt : ∀ᶠ z in nhds z₀, M * ‖φ i z t‖ ^ n < ‖∑ j, ε j * φ i z (c j)‖ ^ n := by
    refine ContinuousAt.eventually_lt (continuousAt_const.mul ((hc t).norm.pow n)) (hcs.norm.pow n) ?_
    simp only [hr0, norm_zero, zero_pow hn0, mul_zero]
    exact pow_pos (norm_pos_iff.2 hs0) n
  obtain ⟨z, hz, h1, h2⟩ := ((hne i z₀ hz₀ a ha).and_eventually (hM.and hlt)).exists
  have h0 : φ i z a * ∑ j, ε j * φ i z (c j) = (∑ j, ε j * φ i z (b j)) * φ i z t := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← map_mul, h j, map_mul]
    ring
  have h3 : ‖φ i z a‖ ^ n * ‖∑ j, ε j * φ i z (c j)‖ ^ n = ‖∑ j, ε j * φ i z (b j)‖ ^ n * ‖φ i z t‖ ^ n := by
    rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, h0]
  have h4 : 0 < ‖φ i z a‖ ^ n := pow_pos (norm_pos_iff.2 hz) n
  have h5 := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg (φ i z t)) n)
  have h6 := mul_lt_mul_of_pos_left h2 h4
  nlinarith
