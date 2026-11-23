import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem end_eq_one_of_pow_prime {V : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {p : ℕ} (hp : p.Prime) (hV : Module.finrank ℚ V + 1 < p) (f : Module.End ℚ V)
    (hf : f ^ p = 1) : f = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : minpoly ℚ f ∣ cyclotomic p ℚ * (X - 1) := by
    rw [cyclotomic_prime_mul_X_sub_one]
    apply minpoly.dvd
    simp [hf]
  have hdeg : (minpoly ℚ f).natDegree ≤ Module.finrank ℚ V := by
    rw [← LinearMap.charpoly_natDegree f]
    exact natDegree_le_of_dvd (LinearMap.minpoly_dvd_charpoly f) (LinearMap.charpoly_monic f).ne_zero
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp.pos
  have hne : minpoly ℚ f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral f)
  have hnd : ¬ cyclotomic p ℚ ∣ minpoly ℚ f := by
    intro h
    have h2 := natDegree_le_of_dvd h hne
    rw [natDegree_cyclotomic, Nat.totient_prime hp] at h2
    omega
  have hcop : IsCoprime (minpoly ℚ f) (cyclotomic p ℚ) :=
    ((hirr.coprime_iff_not_dvd).2 hnd).symm
  have h3 : minpoly ℚ f ∣ X - 1 := hcop.dvd_of_dvd_mul_left h1
  obtain ⟨q, hq⟩ := h3
  have h4 : aeval f (X - 1 : ℚ[X]) = 0 := by
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

theorem gl_eq_one_of_pow_prime (E : Type) [Field E] [NumberField E] (N p : ℕ) (hp : p.Prime)
    (h : Module.finrank ℚ E * N + 1 < p) (γ : GL (Fin N) E) (hγ : γ ^ p = 1) : γ = 1 := by
  have hfin : Module.finrank ℚ (Fin N → E) = Module.finrank ℚ E * N := by
    rw [← Module.finrank_mul_finrank ℚ E (Fin N → E)]
    simp
  have hM : (γ : Matrix (Fin N) (Fin N) E) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hγ, Units.val_one]
  have hg : (Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)) ^ p = 1 := by
    rw [← Matrix.toLin'_pow, hM, Matrix.toLin'_one]; rfl
  have hf : ((Matrix.toLin' (γ : Matrix (Fin N) (Fin N) E)).restrictScalars ℚ :
      Module.End ℚ (Fin N → E)) ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun hg v
    rw [Module.End.pow_apply] at this ⊢
    exact this
  have h1 := end_eq_one_of_pow_prime hp (by rw [hfin]; exact h) _ hf
  apply Units.ext
  apply Matrix.toLin'.injective
  rw [Units.val_one, Matrix.toLin'_one]
  exact LinearMap.ext fun v => LinearMap.congr_fun h1 v

theorem gl_eq_one_of_pow_prime_pow :
    ∀ (E : Type) [Field E] [NumberField E] (N p : ℕ), p.Prime →
      Module.finrank ℚ E * N + 1 < p → ∀ γ : GL (Fin N) E, ∀ a : ℕ, γ ^ (p ^ a) = 1 → γ = 1 := by
  intro E _ _ N p hp h γ a
  induction a with
  | zero => intro h0; simpa using h0
  | succ a ih =>
    intro h0
    apply ih
    apply gl_eq_one_of_pow_prime E N p hp h
    rw [← pow_mul, ← pow_succ]
    exact h0

end GlobalTheory.BadShare
