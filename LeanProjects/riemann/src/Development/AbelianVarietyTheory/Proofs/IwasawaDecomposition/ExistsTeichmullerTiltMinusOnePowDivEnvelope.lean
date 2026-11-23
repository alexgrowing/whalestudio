import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem pow_sub_one_pow_congr_geom_sum_pow {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) (x : R) :
    (l : R) ∣ (x ^ l - 1) ^ (l - 1) - (∑ i ∈ Finset.range l, x ^ i) ^ l := by
  have key : (l : Polynomial ℤ) ∣ (Polynomial.X ^ l - 1) ^ (l - 1) -
      (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℤ) ^ i) ^ l := by
    set y : Polynomial ℤ := Polynomial.X - 1 with hy
    have hy0 : y ≠ 0 := Polynomial.X_sub_C_ne_zero (1 : ℤ)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl y 1
    have hX : y + 1 = Polynomial.X := by rw [hy]; ring
    rw [hX, one_pow] at hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_le).symm⟩
    set s : Polynomial ℤ := ∑ i ∈ Finset.range (k + 1), (Polynomial.X : Polynomial ℤ) ^ i with hs
    have h1 : s * y = Polynomial.X ^ (k + 1) - 1 := geom_sum_mul _ _
    have h2 : s = y ^ k + ((k + 1 : ℕ) : Polynomial ℤ) * r := by
      refine mul_right_cancel₀ hy0 ?_
      rw [h1, hr]; ring
    have h3 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ s - y ^ k := ⟨r, by rw [h2]; ring⟩
    have h4 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ (Polynomial.X ^ (k + 1) - 1) - y ^ (k + 1) :=
      ⟨y * r, by rw [hr]; ring⟩
    have h5 := h3.trans (sub_dvd_pow_sub_pow s (y ^ k) (k + 1))
    have h6 := h4.trans (sub_dvd_pow_sub_pow _ (y ^ (k + 1)) k)
    have h7 := dvd_sub h6 h5
    rw [← pow_mul, ← pow_mul, mul_comm k (k + 1), sub_sub_sub_cancel_right] at h7
    simpa using h7
  simpa [map_sum] using map_dvd (Polynomial.aeval (R := ℤ) x) key

theorem exists_div_prime_pow_dvd {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {l : ℕ} (hl : l.Prime)
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (S : Subalgebra R A) (η z : R)
    (hη : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A η ^ n)
    (hz : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A z ^ n) :
    ∃ w : S, (l : A) * (w : A) = algebraMap R A (η ^ l + l * z) ∧ (l : S) ∣ w ^ l := by
  obtain ⟨g₁, m₁, h₁⟩ := hη l
  obtain ⟨g₂, m₂, h₂⟩ := hη (l * l)
  obtain ⟨g₃, m₃, h₃⟩ := hz l
  have hf : ((l.factorial : ℕ) : A) = (l : A) * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.ne_zero]; push_cast; rfl
  have hb : (((l * l).factorial : ℕ) : A) =
      (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) ^ l * ((l.factorial : ℕ) : A) := by
    rw [← Nat.uniformBell_mul_eq l hl.ne_zero]; push_cast; rfl
  have hg : g₁ ^ l = (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) * g₂ := by
    refine ((hu l).pow l).mul_left_cancel ?_
    rw [← mul_pow, h₁, ← pow_mul, ← h₂, hb]; ring
  let a : S := (((l - 1).factorial : ℕ) : S) * ⟨g₁, m₁⟩
  let b : S := algebraMap R S z
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, map_natCast, ← h₁, hf]
    simp only [a, b]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
    have ha : (l : S) ∣ a ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) ^ l * (Nat.uniformBell l l : S) * (((l - 1).factorial : ℕ) : S) *
        ⟨g₂, m₂⟩, Subtype.ext ?_⟩
      simp only [a]
      push_cast
      rw [mul_pow, hg, hf]; ring
    have hb : (l : S) ∣ b ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) * ⟨g₃, m₃⟩, Subtype.ext ?_⟩
      simp only [b]
      push_cast
      rw [← h₃, hf]; ring
    rw [hr]
    exact dvd_add (dvd_add ha hb) ⟨a * b * r, by ring⟩

theorem exists_dividedPower_mem_Acris0 (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ g ∈ Per.Acris0 l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero).exists_right_inv
  have h : ((n.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) =
      algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by rw [← mul_assoc, hu, one_mul]
  refine ⟨_, ?_, h⟩
  apply GlobalTheory.RingIface.dividedPower_mem_Acris0 <;> assumption

theorem tm_root_pow (l : ℕ) [Fact l.Prime] (e : Per.Fl l) :
    Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = Per.tm e := by
  rw [← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p (Per.Fl l) l e

theorem exists_mu_pow_div_of_isEps (l : ℕ) [hl : Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  set x := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := tm_root_pow l e
  have hmu : mu e = x ^ l - 1 := by rw [hxl]; rfl
  have hθmu : Per.θ l (x ^ l - 1) = 0 := by
    rw [hxl, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self]
  have hθx : Per.θ l (x - 1) ≠ 0 := by
    rw [hx, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_ne_zero]
    exact he.2
  have hη : Per.θ l (∑ i ∈ Finset.range l, x ^ i) = 0 := by
    rw [← geom_sum_mul, map_mul] at hθmu
    exact (mul_eq_zero.1 hθmu).resolve_right hθx
  obtain ⟨z, hz⟩ := pow_sub_one_pow_congr_geom_sum_pow hl.out x
  have hθz : Per.θ l z = 0 := by
    have h := congrArg (Per.θ l) hz
    have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    rw [map_sub, map_pow, map_pow, hθmu, hη, zero_pow h1, zero_pow hl.out.ne_zero, sub_self, map_mul,
      map_natCast] at h
    refine (mul_eq_zero.1 h.symm).resolve_left ?_
    exact_mod_cast hl.out.ne_zero
  obtain ⟨w, hw, hd⟩ := exists_div_prime_pow_dvd hl.out
    (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (Per.Acris0 l) _ z
    (exists_dividedPower_mem_Acris0 l _ hη) (exists_dividedPower_mem_Acris0 l _ hθz)
  refine ⟨w, ?_, hd⟩
  rw [hw, ← hz, add_sub_cancel, map_pow, hmu]

theorem exists_mu_pow_div : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  intro l hl e he
  have step : ∀ m : ℕ, ∀ e : Per.Fl l, e.untilt = 1 →
      (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1 →
      ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
    intro m
    induction m with
    | zero => exact fun e h1 h2 => absurd h1 h2
    | succ m ih =>
      intro e h1 h2
      by_cases h : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = 1
      · obtain ⟨w, hw, hd⟩ := ih _ h h2
        have hmu : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
          rw [xi, mu, mu, geom_sum_mul, tm_root_pow]
        refine ⟨algebraMap _ _ (xi e ^ (l - 1)) * w, ?_, ?_⟩
        · rw [hmu, map_mul, mul_pow, ← hw, ← map_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
          ring
        · rw [mul_pow]
          exact hd.mul_left _
      · exact exists_mu_pow_div_of_isEps l e ⟨h1, h⟩
  by_cases h : ∃ m : ℕ, (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1
  · obtain ⟨m, hm⟩ := h
    exact step m e he hm
  · push Not at h
    have h1 : e = 1 := by
      refine Perfection.ext fun n => ?_
      have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm)^[n] e)
      rw [h n, map_one, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
      exact h2.symm.trans (map_one (PreTilt.coeff (O := Per.OC l) (p := l) n)).symm
    have h0 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    refine ⟨0, ?_, by rw [zero_pow hl.out.ne_zero]; exact dvd_zero _⟩
    have hm : mu e = 0 := by
      rw [h1]
      exact sub_eq_zero.2 (map_one (WittVector.teichmuller l))
    rw [hm, map_zero, zero_pow h0]
    simp

end GlobalTheory.MemLoc
