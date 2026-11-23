import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemRadicalOfHolomorphicRatioTendsto
import Development.AutomorphicArithmetic.DivisorFrames.ExistsComplexPointPrime
import Development.AutomorphicArithmetic.DivisorFrames.ExistsPrimeNonDivisible

open Filter Topology in
theorem UpperTheory.holomorphic_points_vanishing_at_origin :
    ∀ (F A : Type) [Field F] [CommRing A] [IsDomain A] [Algebra F A], Algebra.Smooth F A → ∀ (σ : F →+* ℂ) (m : ℕ) (ε : Fin m → ℂ), (∀ a : Fin m → F, ∑ j, σ (a j) * ε j = 0 → a = 0) → ∀ (p : A) (a : Fin m → A) (M : ℕ), p ≠ 0 → (∀ (ψ : ℂ → (A →+* ℂ)) (r : ℝ), GlobalTheory.ShFam.BdArc.IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, (ψ u).comp (algebraMap F A) = σ) → ψ 0 p = 0 → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ψ u p ≠ 0) → Filter.Tendsto (fun u => (∑ j, ε j * ψ u (a j)) / ψ u (p ^ M)) (nhdsWithin 0 {0}ᶜ) (nhds 0)) → ∀ j, ∃ b : A, a j = b * p ^ M ∧ b ∈ (Ideal.span {p}).radical := by
  intro F A _ _ _ _ hsm σ m ε hε p a M hp h
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing F A
  have : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth F A
  have key : ∀ (P : Ideal A), P.IsPrime → p ∈ P → ∀ (t : A) (c : Fin m → A),
      (∀ j, a j * t = p ^ M * c j) → ∀ j, c j ∈ P := by
    intro P hP hpP t c ht j₀
    by_contra hc0
    obtain ⟨ψ₀, hσ, hP0, hs0⟩ := UpperTheory.exists_complex_point_prime F A σ m ε hε P hP c j₀ hc0
    obtain ⟨ψ, r, hhol, h0, hσ', hne⟩ := GlobalTheory.T.exists_holomorphic_arc_smooth_algebra_nonvanishing F A hsm ψ₀ p hp
    have hlim := h ψ r hhol (fun u hu => (hσ' u hu).trans hσ) (by rw [h0]; exact hP0 p hpP) hne
    have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hhol.1
    have hc : ∀ x, Tendsto (fun u => ψ u x) (𝓝[≠] 0) (𝓝 (ψ₀ x)) := fun x => by
      rw [← h0]
      exact (((hhol.2 x).differentiableAt hball).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
    have h1 := hlim.mul (hc t)
    rw [zero_mul] at h1
    have h2 : Tendsto (fun u => ∑ j, ε j * ψ u (c j)) (𝓝[≠] 0) (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
      have hpu : ψ u (p ^ M) ≠ 0 := by
        rw [map_pow]
        exact pow_ne_zero _ (hne u hu hu0)
      rw [div_mul_eq_mul_div, div_eq_iff hpu, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_assoc, mul_assoc, ← map_mul, ← map_mul, ht j, mul_comm (c j)]
    have h3 : Tendsto (fun u => ∑ j, ε j * ψ u (c j)) (𝓝[≠] 0) (𝓝 (∑ j, ε j * ψ₀ (c j))) :=
      tendsto_finsetSum _ fun j _ => (hc (c j)).const_mul _
    exact hs0 (tendsto_nhds_unique h3 h2)
  have hdvd : ∀ j, p ^ M ∣ a j := by
    by_contra hcon
    obtain ⟨P, t, c, j₀, hP, hd, -, hc, ht⟩ :=
      UpperTheory.exists_prime_non_divisible A m a (p ^ M) (pow_ne_zero M hp) (not_forall.1 hcon)
    exact hc (key P hP (hP.mem_of_pow_mem M hd) t c ht j₀)
  choose b hb using hdvd
  intro j
  refine ⟨b j, by rw [hb j, mul_comm], ?_⟩
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  rintro P ⟨hle, hP⟩
  exact key P hP (hle (Ideal.mem_span_singleton_self p)) 1 b (fun i => by rw [mul_one, hb i]) j
