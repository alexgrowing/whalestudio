import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFormula
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuFinite
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EmultiplicityPowSubOneOdd
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LevelGroupSupLevelInertia

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

section

open KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nlb_nu_le {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem nlb_exists_unit {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

private theorem nlb_main {U : Subgroup ℤ_[l]ˣ} {s e : ℕ} (h : princ l s ≤ U) (he : e ≠ 0) :
    nu l U e ≤ ((max s (if l = 2 then 2 else 1) + e.factorization l : ℕ) : ℕ∞) := by
  have hp : l.Prime := Fact.out
  set a := max s (if l = 2 then 2 else 1) with ha
  have ha1 : 1 ≤ a := le_trans (by split_ifs <;> omega) (le_max_right _ _)
  obtain ⟨u, hu⟩ := nlb_exists_unit (l := l) ha1
  have hm : u ∈ U := h (by
    rw [mem_princ, hu]
    exact pow_dvd_pow _ (le_max_left _ _))
  have hem : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
    rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]
  have key : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ e - 1) =
      emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) + emultiplicity l e := by
    by_cases hl : l = 2
    · refine emultiplicity_pow_sub_one_sq ?_ e
      rw [hu]
      refine pow_dvd_pow _ ?_
      rw [ha, if_pos hl]
      exact le_max_right _ _
    · refine emultiplicity_pow_sub_one_odd hl ?_ e
      rw [hu]
      exact dvd_pow_self _ (by omega)
  have := nlb_nu_le hm e
  rw [key, hem, ← padicValNat_eq_emultiplicity he] at this
  rw [Nat.cast_add, Nat.factorization_def _ hp]
  exact this

end

theorem UpperTheory.V.LDataCardLeFinrank.nuLeBound :
    ∀ (l : ℕ) [Fact l.Prime] (N e : ℕ) (U : Subgroup ℤ_[l]ˣ), KStar.TotallyRealRoots.princ l (N.factorization l) ≤ U → e ≠ 0 → KStar.TotallyRealRoots.nu l U e ≤ (nuBound l N e : ℕ∞) := by
  intro l _ N e U h he
  unfold nuBound
  by_cases hc : l ∣ N ∨ l - 1 ∣ e
  · rw [if_pos hc]
    exact nlb_main h he
  · rw [if_neg hc]
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := KStar.TotallyRealRoots.levelGroup_eq_top (l := l) hc.1 ⊤
    rw [h1] at h2
    have hU : U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      apply h
      rw [KStar.TotallyRealRoots.mem_princ, Nat.factorization_eq_zero_of_not_dvd hc.1, pow_zero]
      exact one_dvd _
    subst hU
    have h3 := hc.2
    rw [← h2, ← KStar.TotallyRealRoots.nu_pos_iff] at h3
    simpa using not_lt.mp h3
