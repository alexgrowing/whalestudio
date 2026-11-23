import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ThetaQuasiPeriods.Change

open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

noncomputable def evalPair {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    Polynomial (MvPolynomial (Fin d) ℂ) →+* ℂ :=
  Polynomial.eval₂RingHom (MvPolynomial.eval z.1) z.2

theorem evalPair_eq {d : ℕ} (z : (Fin d → ℂ) × ℂ) (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    evalPair z r = (r.map (MvPolynomial.eval z.1)).eval z.2 := by
  simp [evalPair, Polynomial.eval_map]

@[simp] theorem evalPair_C {d : ℕ} (z : (Fin d → ℂ) × ℂ) (s : MvPolynomial (Fin d) ℂ) :
    evalPair z (Polynomial.C s) = MvPolynomial.eval z.1 s := by
  simp [evalPair]

@[simp] theorem evalPair_X {d : ℕ} (z : (Fin d → ℂ) × ℂ) :
    evalPair z Polynomial.X = z.2 := by
  simp [evalPair]

theorem continuous_evalPair {d : ℕ} (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    Continuous fun z : (Fin d → ℂ) × ℂ => evalPair z r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | monomial n s =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, evalPair_C, evalPair_X]
    exact ((MvPolynomial.continuous_eval s).comp continuous_fst).mul (continuous_snd.pow n)

theorem points_eq_image_hypersurface {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}
    (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (q q' : MvPolynomial (Fin d) ℂ)
    (hp : ∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r)
    (r : A → Polynomial (MvPolynomial (Fin d) ℂ))
    (hr : ∀ b, j q * b = (r b).eval₂ j.toRingHom a) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (j (q * q')) ≠ 0} =
      (fun (z : (Fin d → ℂ) × ℂ) (b : A) => evalPair z (r b) / MvPolynomial.eval z.1 q) ''
        {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 (q * q') ≠ 0 ∧
          (p.map (MvPolynomial.eval z.1)).eval z.2 = 0} := by
  set E : Polynomial (MvPolynomial (Fin d) ℂ) →+* A :=
    Polynomial.eval₂RingHom j.toRingHom a with hE
  have hEr : ∀ b, E (r b) = j q * b := fun b => (hr b).symm
  have hEC : ∀ s, E (Polynomial.C s) = j s := fun s => by simp [hE]
  ext x
  constructor
  · rintro ⟨φ, rfl, hφ⟩
    let z : (Fin d → ℂ) × ℂ := (fun i => φ (j (MvPolynomial.X i)), φ a)
    have h1 : ∀ s, φ (j s) = MvPolynomial.eval z.1 s := by
      intro s
      induction s using MvPolynomial.induction_on with
      | C c =>
        have : (MvPolynomial.C c : MvPolynomial (Fin d) ℂ) = algebraMap ℂ _ c := rfl
        rw [MvPolynomial.eval_C, this, AlgHom.commutes, AlgHom.commutes]; rfl
      | add s t hs ht => simp only [map_add, hs, ht]
      | mul_X s i hs => simp only [map_mul, hs, MvPolynomial.eval_X, z]
    have h2 : ∀ s, φ (E s) = evalPair z s := by
      intro s
      induction s using Polynomial.induction_on' with
      | add s t hs ht => simp only [map_add, hs, ht]
      | monomial n s =>
        have hX : E Polynomial.X = a := by simp [hE]
        rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow,
          map_pow, evalPair_C, evalPair_X, hEC, h1, hX]
    have hne : MvPolynomial.eval z.1 (q * q') ≠ 0 := by rwa [← h1]
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    refine ⟨z, ⟨hne, ?_⟩, ?_⟩
    · have : E p = 0 := (hp p).2 dvd_rfl
      rw [← evalPair_eq, ← h2, this, map_zero]
    · funext b
      simp only
      rw [← h2, hEr, map_mul, h1]
      field_simp
  · rintro ⟨z, ⟨hne, hz⟩, rfl⟩
    have hq : MvPolynomial.eval z.1 q ≠ 0 := by
      rw [map_mul] at hne; exact left_ne_zero_of_mul hne
    rw [← evalPair_eq] at hz
    have key : ∀ s t, E s = E t → evalPair z s = evalPair z t := by
      intro s t hst
      have h0 : E (s - t) = 0 := by rw [map_sub, hst, sub_self]
      obtain ⟨u, hu⟩ := (hp (s - t)).1 h0
      rw [← sub_eq_zero, ← map_sub, hu, map_mul, hz, zero_mul]
    have hj : ∀ s, evalPair z (r (j s)) / MvPolynomial.eval z.1 q = MvPolynomial.eval z.1 s := by
      intro s
      rw [key (r (j s)) (Polynomial.C (q * s)) (by rw [hEr, hEC, map_mul]), evalPair_C, map_mul]
      field_simp
    let φ : A →ₐ[ℂ] ℂ :=
      { toFun := fun b => evalPair z (r b) / MvPolynomial.eval z.1 q
        map_one' := by simpa using hj 1
        map_zero' := by simpa using hj 0
        map_mul' := by
          intro b c
          have := key (r (b * c) * Polynomial.C q) (r b * r c)
            (by simp only [map_mul, hEr, hEC]; ring)
          simp only [map_mul, evalPair_C] at this
          field_simp
          exact this
        map_add' := by
          intro b c
          have := key (r (b + c)) (r b + r c) (by simp only [map_add, hEr]; ring)
          rw [this, map_add, add_div]
        commutes' := by
          intro c
          have := hj (algebraMap ℂ _ c)
          rw [AlgHom.commutes] at this
          rw [this]
          simp }
    refine ⟨φ, rfl, ?_⟩
    simp only
    rw [hj]
    exact hne

theorem exists_isConnected_principalOpen :
    (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A], ∃ (d : ℕ) (j : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (a : A) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), ringKrullDim A = d ∧ Function.Injective j ∧ j.toRingHom.Finite ∧ p.Monic ∧ Irreducible p ∧ (∀ r : Polynomial (MvPolynomial (Fin d) ℂ), r.eval₂ j.toRingHom a = 0 ↔ p ∣ r) ∧ q ≠ 0 ∧ Polynomial.C q ∈ Ideal.span {p, p.derivative} ∧ ∀ b : A, ∃ r : Polynomial (MvPolynomial (Fin d) ℂ), j q * b = r.eval₂ j.toRingHom a) → (∀ (d : ℕ) (p : Polynomial (MvPolynomial (Fin d) ℂ)) (q : MvPolynomial (Fin d) ℂ), p.Monic → Irreducible p → q ≠ 0 → (∀ x y, MvPolynomial.eval x q ≠ 0 → (p.map (MvPolynomial.eval x)).eval y = 0 → (p.map (MvPolynomial.eval x)).derivative.eval y ≠ 0) → IsConnected {z : (Fin d → ℂ) × ℂ | MvPolynomial.eval z.1 q ≠ 0 ∧ (p.map (MvPolynomial.eval z.1)).eval z.2 = 0}) → (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (f : A), f ≠ 0 → ∃ h : A, h ≠ 0 ∧ IsConnected {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x (h * f) ≠ 0}) := by
  intro H1 H2 A _ _ _ _ f hf
  obtain ⟨d, j, a, p, q, -, hinj, hfin, hmon, hirr, hp, hq, hspan, hr⟩ := H1 A
  choose r hr using hr
  obtain ⟨q', hq', f', hf'⟩ : ∃ q' : MvPolynomial (Fin d) ℂ, q' ≠ 0 ∧ f ∣ j q' := by
    letI : Algebra (MvPolynomial (Fin d) ℂ) A := j.toRingHom.toAlgebra
    haveI : Module.Finite (MvPolynomial (Fin d) ℂ) A := hfin
    have hint : IsIntegral (MvPolynomial (Fin d) ℂ) f := Algebra.IsIntegral.isIntegral f
    exact hint.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)
  have hmul : j q * f' * f = j (q * q') := by rw [map_mul, hf']; ring
  have hqq : q * q' ≠ 0 := mul_ne_zero hq hq'
  refine ⟨j q * f', ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hmul
    exact hqq (hinj (by rw [← hmul, map_zero]))
  · rw [hmul, points_eq_image_hypersurface j a p q q' hp r hr]
    refine (H2 d p (q * q') hmon hirr hqq ?_).image _ ?_
    · intro x y hx hy hd
      obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hspan
      have h := congrArg (evalPair (x, y)) huv
      rw [Polynomial.derivative_map] at hd
      simp only [map_add, map_mul, evalPair_C] at h
      rw [evalPair_eq _ p, evalPair_eq _ p.derivative, hy, hd, mul_zero, mul_zero, add_zero] at h
      rw [map_mul, ← h, zero_mul] at hx
      exact hx rfl
    · refine continuousOn_pi.2 fun b => ContinuousOn.div (continuous_evalPair _).continuousOn
        ((MvPolynomial.continuous_eval q).comp continuous_fst).continuousOn ?_
      intro z hz
      have := hz.1
      rw [map_mul] at this
      exact left_ne_zero_of_mul this

end GlobalTheory
