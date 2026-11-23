import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaChar
open Polynomial

theorem poly_eq_one {Ω : Type} [Field Ω] (p : ℕ) [CharP Ω p] (w : Polynomial Ω) (c : Ω)
    (hd : w.degree < p) (h0 : w.coeff 0 = 1) (h : derivative w = C c * w) : w = 1 := by
  have hw : w ≠ 0 := by rintro rfl; simp at h0
  have hc : c = 0 := by
    by_contra hc
    have h1 := degree_derivative_lt hw
    rw [h, degree_C_mul hc] at h1
    exact lt_irrefl _ h1
  rw [hc, C_0, zero_mul] at h
  ext n
  rcases n with _ | n
  · simpa using h0
  · rw [coeff_one, if_neg (Nat.succ_ne_zero n)]
    by_cases hn : n + 1 < p
    · have h2 := congrArg (fun q => coeff q n) h
      simp only [coeff_derivative, coeff_zero] at h2
      have h3 : ((n : Ω) + 1) ≠ 0 := by
        intro h3
        have : ((n + 1 : ℕ) : Ω) = 0 := by exact_mod_cast h3
        rw [CharP.cast_eq_zero_iff Ω p] at this
        exact absurd (Nat.le_of_dvd (Nat.succ_pos n) this) (by omega)
      exact (mul_eq_zero.1 h2).resolve_right h3
    · apply coeff_eq_zero_of_degree_lt
      exact lt_of_lt_of_le hd (by exact_mod_cast (not_lt.1 hn))

theorem char_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : ∀ (A : Type) [CommRing A] [Algebra Ω A], A → Aˣ), (∀ (A B : Type) [CommRing A] [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (a : A), a ^ p = 0 → u B (f a) = Units.map (f : A →* B) (u A a)) → (∀ (A : Type) [CommRing A] [Algebra Ω A] (a a' : A), a ^ p = 0 → a' ^ p = 0 → u A (a + a') = u A a * u A a') → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → u A a = 1 := by
  intro Ω _ p hp _ u hnat hadd
  have hp2 : 2 ≤ p := hp.out.two_le
  have hp0 : p ≠ 0 := by omega
  have hm : (X ^ p : Polynomial Ω).Monic := monic_X_pow p
  let R := AdjoinRoot (X ^ p : Polynomial Ω)
  let t : R := AdjoinRoot.root (X ^ p : Polynomial Ω)
  have ht : t ^ p = 0 := by
    have := AdjoinRoot.mk_self (f := (X ^ p : Polynomial Ω))
    rwa [map_pow, AdjoinRoot.mk_X] at this
  obtain ⟨w0, hw0⟩ := AdjoinRoot.mk_surjective (g := (X ^ p : Polynomial Ω)) (u R t : R)
  let w : Polynomial Ω := w0 %ₘ (X ^ p)
  have hwd : w.degree < p := by
    have := degree_modByMonic_lt w0 hm
    rwa [degree_X_pow] at this
  have hw : aeval t w = (u R t : R) := by
    rw [← hw0, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_mk]
    have := modByMonic_add_div w0 (X ^ p)
    exact ⟨-(w0 /ₘ X ^ p), by simp only [w]; linear_combination this⟩
  have key : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 →
      (u A a : A) = aeval a w := by
    intro A _ _ a ha
    let f : R →ₐ[Ω] A := Ideal.Quotient.liftₐ (Ideal.span {(X ^ p : Polynomial Ω)}) (aeval a) (by
      intro q hq
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.1 hq
      simp [ha])
    have hf : f t = a := by
      change aeval a (X : Polynomial Ω) = a
      simp
    have h1 := hnat R A f t ht
    rw [hf] at h1
    rw [h1, ← hf, aeval_algHom_apply, hw]
    rfl
  have h0 : w.coeff 0 = 1 := by
    have h1 := hadd Ω 0 0 (zero_pow hp0) (zero_pow hp0)
    rw [add_zero, left_eq_mul] at h1
    have h2 := key Ω 0 (zero_pow hp0)
    rw [h1] at h2
    rw [coeff_zero_eq_aeval_zero, ← h2]; rfl
  have hder : derivative w = C ((derivative w).coeff 0) * w := by
    let D := DualNumber R
    let e : D := DualNumber.eps
    let j : R →ₐ[Ω] D := TrivSqZeroExt.inlAlgHom Ω R R
    have he : e ^ 2 = 0 := by rw [pow_two]; exact DualNumber.eps_mul_eps
    have hep : e ^ p = 0 := pow_eq_zero_of_le hp2 he
    have hs : (j t) ^ p = 0 := by rw [← map_pow, ht, map_zero]
    have hpD : (p : D) = 0 := by
      rw [← map_natCast (algebraMap Ω D), CharP.cast_eq_zero, map_zero]
    have hse : (j t + e) ^ p = 0 := by
      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (j t) e
      rw [hr, hs, hep, hpD]; simp
    have h1 := congrArg Units.val (hadd D (j t) e hs hep)
    rw [Units.val_mul, key D _ hse, key D _ hs, key D _ hep,
      aeval_add_of_sq_eq_zero _ _ _ he] at h1
    have h2 : aeval e w = 1 + algebraMap Ω D ((derivative w).coeff 0) * e := by
      have := aeval_add_of_sq_eq_zero w 0 e he
      rw [zero_add] at this
      rw [this, ← coeff_zero_eq_aeval_zero', ← coeff_zero_eq_aeval_zero', h0, map_one]
    rw [h2, aeval_algHom_apply, aeval_algHom_apply, ← j.commutes, mul_add, _root_.mul_one,
      add_right_inj, ← _root_.mul_assoc, ← map_mul] at h1
    have hsnd : ∀ x : R, TrivSqZeroExt.snd (j x * e) = x := by
      intro x
      change TrivSqZeroExt.snd ((TrivSqZeroExt.inl x : DualNumber R) * DualNumber.eps) = x
      rw [DualNumber.snd_mul]; simp
    have h3 := congrArg TrivSqZeroExt.snd h1
    rw [hsnd, hsnd] at h3
    have h4 : aeval t (derivative w - C ((derivative w).coeff 0) * w) = 0 := by
      rw [map_sub, map_mul, aeval_C, h3]; ring
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h4
    have h5 := eq_zero_of_dvd_of_degree_lt h4 (by
      rw [degree_X_pow]
      refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
      · exact lt_of_le_of_lt degree_derivative_le hwd
      · rw [← smul_eq_C_mul]; exact lt_of_le_of_lt (degree_smul_le _ _) hwd)
    exact sub_eq_zero.1 h5
  have hone := poly_eq_one p w _ hwd h0 hder
  intro A _ _ a ha
  ext
  rw [key A a ha, hone]; simp

end GlobalTheory.AlphaChar
