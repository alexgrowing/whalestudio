import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem coeff_xp {R : Type*} [CommRing R] (k : ℕ) (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (xp k f) = if k ∣ n then PowerSeries.coeff (n / k) f else 0 := by
  rw [xp, PowerSeries.coeff_mk]

theorem xp_eq_expand {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    xp k f = PowerSeries.expand k hk f := by
  ext n
  rw [coeff_xp, PowerSeries.coeff_expand]

theorem xp_add {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f + g) = xp k f + xp k g := by
  ext n
  simp only [coeff_xp, map_add]
  split_ifs <;> simp

theorem xp_sub {R : Type*} [CommRing R] (k : ℕ) (f g : PowerSeries R) : xp k (f - g) = xp k f - xp k g := by
  ext n
  simp only [coeff_xp, map_sub]
  split_ifs <;> simp

theorem xp_mul {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f g : PowerSeries R) :
    xp k (f * g) = xp k f * xp k g := by
  rw [xp_eq_expand hk, xp_eq_expand hk, xp_eq_expand hk, map_mul]

theorem xp_pow {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    xp k (f ^ n) = xp k f ^ n := by
  rw [xp_eq_expand hk, xp_eq_expand hk, map_pow]

theorem xp_C_mul {R : Type*} [CommRing R] (k : ℕ) (c : R) (f : PowerSeries R) :
    xp k (PowerSeries.C c * f) = PowerSeries.C c * xp k f := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_C_mul]
  split_ifs <;> simp

theorem xp_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (f : PowerSeries R) :
    xp k (f.map φ) = (xp k f).map φ := by
  ext n
  simp only [coeff_xp, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem CoeffIn.map_int (R : Subring ℂ) (f : PowerSeries ℤ) : CoeffIn R (f.map (Int.castRingHom ℂ)) := by
  intro n
  rw [PowerSeries.coeff_map, eq_intCast]
  exact intCast_mem R _

theorem CoeffIn.add {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f + g) := by
  intro n
  rw [map_add]
  exact add_mem (hf n) (hg n)

theorem CoeffIn.sub {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f - g) := by
  intro n
  rw [map_sub]
  exact sub_mem (hf n) (hg n)

theorem CoeffIn.mul {R : Subring ℂ} {f g : PowerSeries ℂ} (hf : CoeffIn R f) (hg : CoeffIn R g) :
    CoeffIn R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hf _) (hg _)

theorem CoeffIn.one (R : Subring ℂ) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact one_mem R
  · exact zero_mem R

theorem CoeffIn.pow {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (n : ℕ) : CoeffIn R (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R
  | succ n ih =>
    rw [pow_succ]
    exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ih hf

theorem CoeffIn.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, CoeffIn R (f t)) : CoeffIn R (∏ t ∈ s, f t) := Finset.prod_induction f (ReciprocityTheory.ChartRestriction.L1.CoeffIn R)
    (fun a b ha hb => ReciprocityTheory.ChartRestriction.L1.CoeffIn.mul ha hb) (ReciprocityTheory.ChartRestriction.L1.CoeffIn.one R) hf

theorem CoeffIn.xp {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (xp k f) := by
  intro n
  rw [coeff_xp]
  split_ifs
  · exact hf _
  · exact zero_mem R

theorem CoeffIn.sub1 {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) {c : ℂ} (hc : c ∈ R) (k : ℕ) :
    CoeffIn R (sub1 c k f) := by
  have hr : ReciprocityTheory.ChartRestriction.L1.CoeffIn R (PowerSeries.rescale c f) := fun m => by
    rw [PowerSeries.coeff_rescale]
    exact mul_mem (pow_mem hc m) (hf m)
  exact ReciprocityTheory.ChartRestriction.L1.CoeffIn.xp hr k

theorem LowUnit.mul {R : Subring ℂ} {f g : PowerSeries ℂ} {n n' : ℕ} {u u' : ℂ} (hf : LowUnit R f n u)
    (hg : LowUnit R g n' u') : LowUnit R (f * g) (n + n') (u * u') := by
  obtain ⟨hu, hui, hu0, hlow, hc⟩ := hf
  obtain ⟨hu', hui', hu0', hlow', hc'⟩ := hg
  refine ⟨mul_mem hu hu', by rw [mul_inv]; exact mul_mem hui hui', mul_ne_zero hu0 hu0', ?_, ?_⟩
  · intro m hm
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 < n
    · rw [hlow _ h1, zero_mul]
    · rw [hlow' _ (by omega), mul_zero]
  · rw [PowerSeries.coeff_mul, Finset.sum_eq_single (n, n')]
    · rw [hc, hc']
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h1 : p.1 < n
      · rw [hlow _ h1, zero_mul]
      · have h2 : p.2 < n' := by
          by_contra h2
          exact hne (Prod.ext (by show p.1 = n; omega) (by show p.2 = n'; omega))
        rw [hlow' _ h2, mul_zero]
    · intro h
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (rfl : n + n' = n + n')) h

theorem LowUnit.one (R : Subring ℂ) : LowUnit R 1 0 1 := by
  refine ⟨one_mem R, by rw [inv_one]; exact one_mem R, one_ne_zero,
    fun n hn => absurd hn (Nat.not_lt_zero n), ?_⟩
  simp

theorem LowUnit.prod {R : Subring ℂ} {α : Type*} (s : Finset α) (f : α → PowerSeries ℂ)
    (hf : ∀ t ∈ s, ∃ n u, LowUnit R (f t) n u) : ∃ n u, LowUnit R (∏ t ∈ s, f t) n u := Finset.prod_induction f (fun g => ∃ n u, ReciprocityTheory.ChartRestriction.L1.LowUnit R g n u)
    (fun a b ⟨n, u, ha⟩ ⟨n', u', hb⟩ => ⟨n + n', u * u', ReciprocityTheory.ChartRestriction.L1.LowUnit.mul ha hb⟩)
    ⟨0, 1, ReciprocityTheory.ChartRestriction.L1.LowUnit.one R⟩ hf

end ReciprocityTheory.ChartRestriction.L1
