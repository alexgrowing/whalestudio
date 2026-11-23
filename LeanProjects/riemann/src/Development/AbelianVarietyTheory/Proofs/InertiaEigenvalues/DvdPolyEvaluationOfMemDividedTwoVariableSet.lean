import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomExtDense
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism GlobalTheory.CrysEval
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.CrysEval

theorem coeff_natCast_mul_ps {R : Type} [CommRing R] (n i : ℕ) (f : R⟦X⟧) :
    coeff i ((n : R⟦X⟧) * f) = n * coeff i f := by
  rw [← map_natCast (C : R →+* R⟦X⟧) n, coeff_C_mul]

theorem dvd_fP_of_mem_PPSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (ϖ : PiSys l e) (g : ↥(GK (ϖ.field a))) (b : Bp l a) (F : ZMod a → K⟦X⟧⟦X⟧), F ∈ PPSet t K e → ∀ n : ℕ, n ≠ 0 → (n : ZMod a → K⟦X⟧⟦X⟧) * F = iotaP K t b → ∃ y : Per.Acris l, (n : Per.Acris l) * y = fP a ϖ (g : GQ l) b := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ g b F hF n hn hnF
  obtain ⟨w, -, hw⟩ := hF
  have := charZero_K (l := l) (K := K)
  have key : ∀ i k, ((i.factorial * (k / e).factorial : ℕ) : Wq l a) * (b.coeff i).coeff k = n * w (i, k) := by
    intro i k
    apply embK_injective (K := K) t 0
    have h1 := congrArg (fun G => coeff k (coeff i (G 0))) hnF
    simp only [Pi.mul_apply, Pi.natCast_apply] at h1
    rw [coeff_natCast_mul_ps, coeff_natCast_mul_ps, coeff_iotaP] at h1
    have h2 := hw 0 i k
    change _ = embK K t 0 (w (i, k)) at h2
    rw [map_mul, map_mul, map_natCast, map_natCast]
    push_cast at h2 ⊢
    linear_combination (-((i.factorial : K) * ((k / e).factorial : K))) * h1 + (n : K) * h2
  have hμ := ϖ.theta_mu (ϖ.gal_pi a g)
  set T := ainfToAcris l ϖ.teich with hTdef
  have term : ∀ i k, ainfToAcris l (wA l a ((b.coeff i).coeff k)) * T ^ k *
      ainfToAcris l (ϖ.mu (g : GQ l) * ϖ.teich) ^ i ∈ Ideal.span {(n : Per.Acris l)} := by
    intro i k
    obtain ⟨D, hD⟩ := ϖ.exists_dpow_teich (k / e)
    have hm := factorial_mul_dpow (ϖ.mu (g : GQ l)) hμ i
    have hk := congrArg (fun x => ainfToAcris l (wA l a x)) (key i k)
    simp only [map_mul, map_natCast] at hk
    push_cast at hk
    rw [Ideal.mem_span_singleton']
    refine ⟨ainfToAcris l (wA l a (w (i, k))) * D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i, ?_⟩
    have hT : T ^ k = T ^ (k % e) * T ^ (e * (k / e)) := by rw [← pow_add, Nat.mod_add_div]
    rw [hT, ← hD, map_mul, mul_pow, ← hm]
    linear_combination (-(D * dpow (ϖ.mu (g : GQ l)) hμ i * T ^ (k % e) * T ^ i)) * hk
  have hmem : fP a ϖ (g : GQ l) b ∈ Ideal.span {(n : Per.Acris l)} := by
    rw [fP, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Ideal.sum_mem _ fun i _ => ?_
    have hev : evC a ϖ (b.coeff i) = (b.coeff i).sum fun k c => ainfToAcris l (wA l a c) * T ^ k := by
      rw [evC, RingHom.comp_apply, RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, ev_coe,
        Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def]
      change ainfToAcris l _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, map_pow]
      rfl
    rw [hev, Polynomial.sum_def, Finset.sum_mul]
    exact Ideal.sum_mem _ fun k _ => term i k
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [mul_comm]; exact hy⟩

end GlobalTheory.CrysEval
