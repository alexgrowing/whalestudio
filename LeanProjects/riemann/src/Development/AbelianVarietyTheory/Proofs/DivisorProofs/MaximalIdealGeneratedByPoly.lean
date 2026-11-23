import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart

namespace GlobalTheory.EtaleUnif

open Polynomial

theorem exists_map_eq_C_mul {k K : Type} [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] (f : K[X]) :
    ∃ c : k, c ≠ 0 ∧ ∃ P : k[X], P.map (algebraMap k K) = C (algebraMap k K c) * f := by
  obtain ⟨c, hc, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors k) f
  refine ⟨c, nonZeroDivisors.ne_zero hc, _, hP.trans ?_⟩
  rw [← smul_eq_C_mul, algebraMap_smul]

theorem exists_poly_simple_zero_dvd_vanishing {k K : Type} [CommRing k] [IsDomain k] [Field K] [Algebra k K]
    [IsFractionRing k K] [Algebra K ℂ] (w : ℂ) :
    ∃ P : k[X], aeval w (P.map (algebraMap k K)) = 0 ∧
      (P = 0 ∨ aeval w (P.derivative.map (algebraMap k K)) ≠ 0) ∧
      ∀ g : k[X], aeval w (g.map (algebraMap k K)) = 0 →
        ∃ d : k, d ≠ 0 ∧ ∃ h : k[X], C d * g = P * h := by
  haveI : CharZero K := (algebraMap K ℂ).charZero
  have hinj : Function.Injective (Polynomial.map (algebraMap k K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective k K)
  by_cases hw : IsAlgebraic K w
  · have hint : IsIntegral K w := hw.isIntegral
    obtain ⟨c, hc, P, hP'⟩ := exists_map_eq_C_mul (k := k) (minpoly K w)
    refine ⟨P, ?_, Or.inr ?_, ?_⟩
    · rw [hP', map_mul, minpoly.aeval, mul_zero]
    · rw [← derivative_map, hP', derivative_C_mul, map_mul, aeval_C]
      have hsep : (minpoly K w).Separable := (minpoly.irreducible hint).separable
      have hc' : algebraMap k K c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective k K)).2 hc
      exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K ℂ).injective).2 hc')
        (hsep.aeval_derivative_ne_zero (minpoly.aeval K w))
    · intro g hg
      obtain ⟨hK, hhK⟩ : minpoly K w ∣ g.map (algebraMap k K) := minpoly.dvd K w hg
      obtain ⟨d, hd, H, hH'⟩ := exists_map_eq_C_mul (k := k) hK
      refine ⟨c * d, mul_ne_zero hc hd, H, ?_⟩
      apply hinj
      rw [Polynomial.map_mul, Polynomial.map_mul, hP', hH', hhK, Polynomial.map_C, map_mul, C_mul]
      ring
  · refine ⟨0, by simp, Or.inl rfl, ?_⟩
    intro g hg
    refine ⟨1, one_ne_zero, 0, ?_⟩
    have h0 : g.map (algebraMap k K) = 0 := by
      by_contra hne0
      exact hw ⟨_, hne0, hg⟩
    have : g = 0 := hinj (by rw [h0, Polynomial.map_zero])
    rw [this, mul_zero, mul_zero]

theorem exists_poly_simple_zero {k : Type} [CommRing k] (σ : k →+* ℂ)
    (hσ : Function.Injective σ) (w : ℂ) :
    ∃ P : k[X], P.eval₂ σ w = 0 ∧ (P = 0 ∨ P.derivative.eval₂ σ w ≠ 0) ∧
      ∀ g : k[X], g.eval₂ σ w = 0 → ∃ d : k, d ≠ 0 ∧ ∃ h : k[X], C d * g = P * h := by
  haveI : IsDomain k := hσ.isDomain σ
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : K →+* ℂ, τ.comp (algebraMap k K) = σ := by
    refine ⟨IsFractionRing.lift (A := k) (K := K) (g := σ) hσ, ?_⟩
    ext a
    rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]
  letI : Algebra K ℂ := τ.toAlgebra
  have hτ' : (algebraMap K ℂ).comp (algebraMap k K) = σ := hτ
  have hev : ∀ g : k[X], aeval w (g.map (algebraMap k K)) = g.eval₂ σ w := by
    intro g
    rw [aeval_def, eval₂_map, hτ']
  have := exists_poly_simple_zero_dvd_vanishing (k := k) (K := K) w
  simp only [hev] at this
  exact this

theorem maximalIdeal_eq_map_under (B A R : Type) [CommRing B] [CommRing A] [CommRing R]
    [IsLocalRing R] [Algebra B A] [Algebra.Etale B A] [Algebra A R] (q : Ideal A) [q.IsPrime]
    [IsLocalization.AtPrime R q] :
    IsLocalRing.maximalIdeal R = ((q.under B).map (algebraMap B A)).map (algebraMap A R) := by
  let p : Ideal B := q.under B
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hun : Algebra.IsUnramifiedAt B q := inferInstance
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq B p q).mp hun).2
  have h1 : q.map (algebraMap A (Localization.AtPrime q)) =
      (p.map (algebraMap B A)).map (algebraMap A (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hm]
  let ε := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) R
  have hcomp : (ε : Localization.AtPrime q →+* R).comp (algebraMap A (Localization.AtPrime q)) =
      algebraMap A R := by
    ext a
    simp
  have h2 := congrArg (Ideal.map (ε : Localization.AtPrime q →+* R)) h1
  rw [Ideal.map_map, Ideal.map_map, hcomp] at h2
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q R]
  exact h2

end GlobalTheory.EtaleUnif

namespace GlobalTheory

open Polynomial in

theorem etale_maximalIdeal_span_poly (k A R : Type) [CommRing k] [CommRing A] [CommRing R]
    [IsLocalRing R] [Algebra A R] (φ : MvPolynomial (Fin 1) k →+* A) (hφ : φ.Etale)
    (e : A →+* ℂ) (he : Function.Injective (e.comp (φ.comp MvPolynomial.C)))
    (q : Ideal A) [q.IsPrime] [IsLocalization.AtPrime R q] (hq : q = RingHom.ker e) :
    ∃ P : Polynomial k, IsLocalRing.maximalIdeal R = Ideal.span {algebraMap A R
        (P.eval₂ (φ.comp MvPolynomial.C) (φ (MvPolynomial.X 0)))} ∧
      (P = 0 ∨ P.derivative.eval₂ (e.comp (φ.comp MvPolynomial.C)) (e (φ (MvPolynomial.X 0))) ≠ 0) := by
  obtain ⟨P, hP0, hPd, hP⟩ :=
    EtaleUnif.exists_poly_simple_zero (e.comp (φ.comp MvPolynomial.C)) he (e (φ (MvPolynomial.X 0)))
  refine ⟨P, ?_, hPd⟩
  letI := φ.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) k) A := hφ
  have hmax := EtaleUnif.maximalIdeal_eq_map_under (MvPolynomial (Fin 1) k) A R q
  have hev : ∀ (f : k[X]), e (f.eval₂ (φ.comp MvPolynomial.C) (φ (MvPolynomial.X 0))) =
      f.eval₂ (e.comp (φ.comp MvPolynomial.C)) (e (φ (MvPolynomial.X 0))) := fun f =>
    Polynomial.hom_eval₂ f _ e _
  have hkey : ∀ g : MvPolynomial (Fin 1) k, φ g =
      (MvPolynomial.uniqueAlgEquiv k (Fin 1) g).eval₂ (φ.comp MvPolynomial.C)
        (φ (MvPolynomial.X 0)) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simp [hf, hg, Polynomial.eval₂_add]
    | mul_X f i hf =>
      have : i = 0 := Subsingleton.elim _ _
      subst this
      simp [hf, Polynomial.eval₂_mul]
  apply le_antisymm
  · rw [hmax, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro g hg
    have hg' : φ g ∈ q := hg
    have hzero : (MvPolynomial.uniqueAlgEquiv k (Fin 1) g).eval₂
        (e.comp (φ.comp MvPolynomial.C)) (e (φ (MvPolynomial.X 0))) = 0 := by
      rw [← hev, ← hkey, ← RingHom.mem_ker, ← hq]
      exact hg'
    obtain ⟨d, hd, h, hh⟩ := hP _ hzero
    have hA := congrArg (Polynomial.eval₂ (φ.comp MvPolynomial.C) (φ (MvPolynomial.X 0))) hh
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C, ← hkey] at hA
    have hnot : (φ.comp MvPolynomial.C) d ∈ q.primeCompl := by
      intro hmem
      have hmem' : (φ.comp MvPolynomial.C) d ∈ q := hmem
      rw [hq, RingHom.mem_ker] at hmem'
      exact hd (he (by simpa using hmem'))
    have hu : IsUnit (algebraMap A R ((φ.comp MvPolynomial.C) d)) :=
      IsLocalization.map_units R (⟨_, hnot⟩ : q.primeCompl)
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    have hR := congrArg (algebraMap A R) hA
    rw [map_mul, map_mul] at hR
    have hdv : algebraMap A R (P.eval₂ (φ.comp MvPolynomial.C) (φ (MvPolynomial.X 0))) ∣
        algebraMap A R ((φ.comp MvPolynomial.C) d) * algebraMap A R (φ g) := ⟨_, hR⟩
    exact (hu.dvd_mul_left).1 hdv
  · rw [Ideal.span_singleton_le_iff_mem, ← IsLocalization.AtPrime.map_eq_maximalIdeal q R]
    apply Ideal.mem_map_of_mem
    rw [hq, RingHom.mem_ker, hev]
    exact hP0

end GlobalTheory
