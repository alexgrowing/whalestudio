import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FlatMapMaximalIdealIsSeparable
open GlobalTheory.EtC

namespace GlobalTheory.LocalIndEtAIC

open Polynomial IsLocalRing

theorem lift_atComap {W O : Type} [CommRing W] [CommRing O] [IsLocalRing O] (v : W →+* O) :
    ∃ φ : Localization.AtPrime ((maximalIdeal O).comap v) →+* O,
      ∀ w, φ (algebraMap W _ w) = v w := by
  have hu : ∀ y : ((maximalIdeal O).comap v).primeCompl, IsUnit (v y) := fun y => by
    by_contra hy
    exact y.2 hy
  exact ⟨IsLocalization.lift hu, fun w => IsLocalization.lift_eq hu w⟩

theorem isDomain_aic_of_indEt : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O],
    IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime],
      IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  intro T O _ _ _ _ h hE
  have hdom : IsDomain O := by
    refine @NoZeroDivisors.to_isDomain O _ _ ⟨fun {x y} hxy => ?_⟩
    let I : Ideal (MvPolynomial (Fin 2) T) := Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1}
    haveI : Algebra.FinitePresentation T (MvPolynomial (Fin 2) T ⧸ I) :=
      Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
    let g : (MvPolynomial (Fin 2) T ⧸ I) →ₐ[T] O :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval ![x, y]) (by
        intro a ha
        obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hxy])
    obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
    let w : Fin 2 → W := fun i => u (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
    have hw : ∀ i, v (w i) = ![x, y] i := fun i => by
      have := DFunLike.congr_fun huv (Ideal.Quotient.mkₐ T I (MvPolynomial.X i))
      exact this.trans (MvPolynomial.aeval_X _ i)
    have h0 : w 0 * w 1 = 0 := by
      have : Ideal.Quotient.mkₐ T I (MvPolynomial.X 0) * Ideal.Quotient.mkₐ T I (MvPolynomial.X 1) = 0 := by
        rw [← map_mul]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      simp only [w, ← map_mul, this, map_zero]
    obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
    haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
    have hm : algebraMap W (Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))) (w 0) *
        algebraMap W _ (w 1) = 0 := by rw [← map_mul, h0, map_zero]
    rcases mul_eq_zero.mp hm with h1 | h1
    · left
      have e := hφ (w 0)
      rw [h1, map_zero] at e
      have := hw 0
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
    · right
      have e := hφ (w 1)
      rw [h1, map_zero] at e
      have := hw 1
      simp only [AlgHom.coe_toRingHom] at e
      rw [← e] at this
      simpa using this.symm
  refine ⟨hdom, ?_⟩
  intro p hpm hdeg
  set n := p.natDegree with hn
  let g : MvPolynomial (Fin n) T →ₐ[T] O := MvPolynomial.aeval (fun i => p.coeff i)
  obtain ⟨W, _, _, _, u, v, huv⟩ := GlobalTheory.IndEtaleLocal.exists_etale_factor h g
  let c : Fin n → W := fun i => u (MvPolynomial.X i)
  have hc : ∀ i, v (c i) = p.coeff i := fun i => by
    have := DFunLike.congr_fun huv (MvPolynomial.X i)
    exact this.trans (MvPolynomial.aeval_X _ i)
  let p' : W[X] := X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp'm : p'.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hp' : p'.map (v : W →+* O) = p := by
    conv_rhs => rw [hpm.as_sum]
    simp only [p', Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Polynomial.map_mul, Polynomial.map_C]
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
    simp [hc]
    rfl
  have hp'd : p'.natDegree = n := by
    have e1 := hp'm.natDegree_map (v : W →+* O)
    rw [hp'] at e1
    rw [← e1]
  obtain ⟨φ, hφ⟩ := lift_atComap (v : W →+* O)
  set L := Localization.AtPrime ((maximalIdeal O).comap (v : W →+* O))
  haveI := (hE W ((maximalIdeal O).comap (v : W →+* O))).1
  have hL := (hE W ((maximalIdeal O).comap (v : W →+* O))).2
  have hmL : (p'.map (algebraMap W L)).Monic := hp'm.map _
  have hdL : 0 < (p'.map (algebraMap W L)).natDegree := by
    rw [hp'm.natDegree_map, hp'd]; exact hdeg
  obtain ⟨r, hr⟩ := hL _ hmL hdL
  refine ⟨φ r, ?_⟩
  have hcomp : φ.comp (algebraMap W L) = (v : W →+* O) := RingHom.ext hφ
  have hpL : p = (p'.map (algebraMap W L)).map φ := by rw [Polynomial.map_map, hcomp, hp']
  rw [hpL, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]

end GlobalTheory.LocalIndEtAIC
