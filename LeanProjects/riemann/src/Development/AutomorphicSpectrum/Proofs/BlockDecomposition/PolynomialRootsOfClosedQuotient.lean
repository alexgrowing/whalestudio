import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.RootsUpToUnits

theorem subsingleton_of_mul_eq_one {S : Type} [CommRing S] {ϖ c : S}
    (hJ : ϖ ∈ (⊥ : Ideal S).jacobson) (h : ϖ * c = 1) : Subsingleton S := by
  have hu := (Ideal.mem_jacobson_bot.mp hJ) (-c)
  rw [mul_neg, h, neg_add_cancel] at hu
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu)

theorem normal_form {S : Type} [CommRing S] (ϖ : S) (h : ∀ f : S, ϖ ∣ f ∨ f ∣ ϖ) (f : S) (M : ℕ) :
    ϖ ^ M ∣ f ∨ ∃ (j : ℕ) (f' : S), f = ϖ ^ j * f' ∧ f' ∣ ϖ := by
  induction M generalizing f with
  | zero => left; simp
  | succ M ih =>
    rcases h f with ⟨g, rfl⟩ | hf
    · rcases ih g with hg | ⟨j, f', rfl, hf'⟩
      · left; rw [pow_succ']; exact mul_dvd_mul_left ϖ hg
      · right; exact ⟨j + 1, f', by ring, hf'⟩
    · right; exact ⟨0, f, by simp, hf⟩

theorem root_of_dvd {S : Type} [CommRing S] {ϖ g : S} (hJ : ϖ ∈ (⊥ : Ideal S).jacobson)
    (hA : Aic (S ⧸ Ideal.span {ϖ ^ 2})) (hg : g ∣ ϖ) {i : ℕ} (hi : 0 < i) :
    ∃ (r : S) (u : Sˣ), g = u * r ^ i := by
  obtain ⟨h, hh⟩ := hg
  by_cases hn : Nontrivial (S ⧸ Ideal.span {ϖ ^ 2})
  · haveI := hn
    obtain ⟨x, hx⟩ := hA (Polynomial.X ^ i - Polynomial.C (Ideal.Quotient.mk _ g))
      (Polynomial.monic_X_pow_sub_C _ hi.ne') (by rw [Polynomial.natDegree_X_pow_sub_C]; exact hi)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) r) ^ i - Ideal.Quotient.mk (Ideal.span {ϖ ^ 2}) g = 0 := by
      simpa using hx
    have hmem : r ^ i - g ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
      exact hx'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hmem
    have hu := (Ideal.mem_jacobson_bot.mp hJ) (t * h)
    have key : r ^ i = g * (ϖ * (t * h) + 1) := by
      have e1 : r ^ i = g + t * ϖ ^ 2 := by rw [ht]; ring
      rw [e1, hh]; ring
    refine ⟨r, hu.unit⁻¹, ?_⟩
    rw [key]
    calc g = ((↑hu.unit⁻¹ : S) * (ϖ * (t * h) + 1)) * g := by rw [hu.val_inv_mul, one_mul]
      _ = (↑hu.unit⁻¹ : S) * (g * (ϖ * (t * h) + 1)) := by ring
  · have hs : Subsingleton (S ⧸ Ideal.span {ϖ ^ 2}) := not_nontrivial_iff_subsingleton.mp hn
    have h1 : (1 : S) ∈ Ideal.span {ϖ ^ 2} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]; exact Subsingleton.elim _ _
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp h1
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := ϖ * a) hJ (by rw [← ha]; ring)
    exact ⟨1, 1, Subsingleton.elim _ _⟩

theorem roots_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson →
    ϖ ∈ nonZeroDivisors S → Dich ϖ → Aic (S ⧸ Ideal.span {ϖ ^ 2}) → Roots ϖ := by
  intro S _ ϖ hJ hϖ hD hA f N i hf hi
  have hdich : ∀ g : S, ϖ ∣ g ∨ g ∣ ϖ := fun g =>
    hD g ϖ ⟨1, by rw [pow_one]; exact Ideal.subset_span (by simp)⟩
  rcases normal_form ϖ hdich f (N + 1) with hM | ⟨j, f', rfl, hf'⟩
  · obtain ⟨k, hk⟩ := dvd_trans hM hf
    have e0 : (1 - ϖ * k) * ϖ ^ N = 0 := by linear_combination hk
    have e1 : 1 - ϖ * k = 0 := (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hϖ N)).mp e0
    have hS : Subsingleton S := subsingleton_of_mul_eq_one (c := k) hJ (by linear_combination -e1)
    exact ⟨1, 1, Subsingleton.elim _ _⟩
  · obtain ⟨r0, u0, h0⟩ := root_of_dvd hJ hA (dvd_refl ϖ) hi
    obtain ⟨r, u, hr⟩ := root_of_dvd hJ hA hf' hi
    refine ⟨r0 ^ j * r, u0 ^ j * u, ?_⟩
    rw [hr, h0]; push_cast; ring

end GlobalTheory.CompanionTheory.RootsUpToUnits
