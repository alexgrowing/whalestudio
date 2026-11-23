import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace MinkDiv

variable {A : Type} [AddCommGroup A]

theorem iterate_eq (f g : A →+ A) (hfg : ∀ z, f z = z + g z) (y : A) (hy : g (g (g y)) = 0)
    (n : ℕ) : f^[n] y = y + n • g y + (n.choose 2) • g (g y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_add, map_add, map_nsmul, map_nsmul, hfg y,
      hfg (g y), hfg (g (g y)), hy, Nat.choose_succ_succ' n 1, Nat.choose_one_right]
    simp only [add_nsmul, smul_add, one_nsmul, add_zero]
    abel

theorem prime_case (l p : ℕ) (hl : l.Prime) (ho : Odd l) (hp : p.Prime) (f : A →+ A)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x)
    (hord : ∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[p] x = x)
    (hfix : ∀ x : A, l • x = 0 → f x = x) :
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  set g : A →+ A := f - AddMonoidHom.id A with hg
  have hfg : ∀ z, f z = z + g z := fun z => by simp [hg]
  have key : ∀ k : ℕ, ∀ x : A, l ^ (k + 1) • x = 0 → g x = 0 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have := hfix x (by simpa using hx)
      simp [hg, this]
    | succ k ih =>
      intro x hx
      have h1 : ∀ z : A, l • z = 0 → g z = 0 := fun z hz =>
        ih z (by rw [pow_succ, mul_smul, hz, smul_zero])
      have h2 : ∀ z : A, l ^ (k + 1 + 1) • z = 0 → l • g z = 0 := fun z hz => by
        rw [← map_nsmul]
        exact ih _ (by rw [← mul_smul, ← pow_succ]; exact hz)
      by_cases hpl : p = l
      · subst hpl
        obtain ⟨y, rfl⟩ := hdiv x
        have hy : p ^ (k + 1 + 1 + 1) • y = 0 := by rw [pow_succ, mul_smul]; exact hx
        have e1 : p • p • g y = 0 := by
          rw [← map_nsmul g p y]; exact h2 _ hx
        have e2 : p • g (g y) = 0 := by
          apply h2
          rw [pow_succ, pow_succ, mul_smul, mul_smul, e1, smul_zero]
        have e3 : g (g (g y)) = 0 := h1 _ e2
        have e4 := iterate_eq f g hfg y e3 p
        rw [hord y _ hy] at e4
        have h3 : 2 < p := by
          rcases hp.two_le.lt_or_eq with h | h
          · exact h
          · subst h; exact absurd ho (by decide)
        obtain ⟨c, hc⟩ := hp.dvd_choose_self (k := 2) (by norm_num) h3
        rw [hc, mul_comm, mul_smul, e2, smul_zero, add_zero] at e4
        rw [map_nsmul]
        exact (add_eq_left.mp e4.symm)
      · have e1 : l • g x = 0 := h2 x hx
        have e2 : g (g x) = 0 := h1 _ e1
        have e4 := iterate_eq f g hfg x (by rw [e2, map_zero]) p
        rw [hord x _ hx, e2, smul_zero, add_zero] at e4
        have e5 : p • g x = 0 := add_eq_left.mp e4.symm
        have hc : Nat.Coprime p l := (Nat.coprime_primes hp hl).mpr hpl
        have d1 := addOrderOf_dvd_of_nsmul_eq_zero e5
        have d2 := addOrderOf_dvd_of_nsmul_eq_zero e1
        have d3 := Nat.dvd_gcd d1 d2
        rw [hc, Nat.dvd_one] at d3
        exact AddMonoid.addOrderOf_eq_one_iff.mp d3
  intro a x hx
  have := key a x (by rw [pow_succ', mul_smul, hx, smul_zero])
  rw [hfg, this, add_zero]

theorem add_case (l : ℕ) (hl : l.Prime) (ho : Odd l)
    (hdiv : ∀ x : A, ∃ y : A, l • y = x) (r : ℕ) (hr : r ≠ 0) :
    ∀ f : AddMonoid.End A, (∀ (x : A) (a : ℕ), l ^ a • x = 0 → f^[r] x = x) →
    (∀ x : A, l • x = 0 → f x = x) →
    ∀ (a : ℕ) (x : A), l ^ a • x = 0 → f x = x := by
  induction r using induction_on_primes with
  | zero => exact absurd rfl hr
  | one => intro f h _ a x hx; exact h x a hx
  | prime_mul p b hp ih =>
    intro f hord hfix
    have hb : b ≠ 0 := by rintro rfl; simp at hr
    have hc : ((f ^ p : AddMonoid.End A) : A → A) = f^[p] := AddMonoid.End.coe_pow _ _ _
    have := ih hb (f ^ p)
      (fun x a hx => by rw [hc, ← Function.iterate_mul]; exact hord x a hx)
      (fun x hx => by rw [hc]; exact Function.iterate_fixed (hfix x hx) p)
    exact prime_case l p hl ho hp f hdiv
      (fun x a hx => by have h := this a x hx; rw [hc] at h; exact h) hfix

end MinkDiv

theorem minkowski_divisible : ∀ (Q : Type) [CommGroup Q] (l : ℕ) (u : Q ≃* Q) (r : ℕ), l.Prime → Odd l → 0 < r → (∀ x : Q, ∃ y : Q, y ^ l = x) → (∀ x, u^[r] x = x) → (∀ x, x ^ l = 1 → u x = x) → ∀ (x : Q) (a : ℕ), x ^ (l ^ a) = 1 → u x = x := by
  intro Q _ l u r hl ho hr hdiv hord hfix x a hx
  exact MinkDiv.add_case (A := Additive Q) l hl ho (fun x => hdiv x.toMul) r hr.ne'
    (MonoidHom.toAdditive u.toMonoidHom) (fun x _ _ => hord x.toMul) (fun x hx => hfix x.toMul hx)
    a (Additive.ofMul x) hx

end GlobalTheory
