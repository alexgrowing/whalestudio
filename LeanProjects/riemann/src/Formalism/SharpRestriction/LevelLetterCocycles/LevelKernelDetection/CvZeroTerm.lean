import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

open PowerSeries

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

def cv (f : PowerSeries R) (g : ℤ → M) (k : ℤ) : M := ∑ᶠ j : ℕ, coeff j f • g (k - j)

theorem cv_eq_sum (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : cv f g k = ∑ j ∈ Finset.range N, coeff j f • g (k - j) := by
  unfold cv
  apply finsum_eq_sum_of_support_subset
  intro j hj
  rw [Function.mem_support] at hj
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hjN
  exact hj (by rw [hg _ (by omega), smul_zero])

theorem cv_low (f : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) (hk : k < m) :
    cv f g k = 0 := by
  rw [cv_eq_sum f g m hg k 0 (by omega), Finset.sum_range_zero]

theorem cv_vanish (f : PowerSeries R) (g : ℤ → M) (hg : ∀ k < 0, g k = 0) (N : ℕ)
    (hf : (X : PowerSeries R) ^ N ∣ f) (k : ℤ) (hk : k < N) : cv f g k = 0 := by
  rw [cv_eq_sum f g 0 hg k N (by omega)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [PowerSeries.X_pow_dvd_iff.mp hf j (Finset.mem_range.mp hj), zero_smul]

theorem cv_zero_term (f : PowerSeries R) (g : ℤ → M) (hg : ∀ k < 0, g k = 0) :
    cv f g 0 = constantCoeff f • g 0 := by
  rw [cv_eq_sum f g 0 hg 0 1 (by omega), Finset.sum_range_one]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem cv_add (f : PowerSeries R) (g g' : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0)
    (hg' : ∀ k < m, g' k = 0) (k : ℤ) : cv f (g + g') k = cv f g k + cv f g' k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  have hs : ∀ j < m, (g + g') j = 0 := fun j hj => by
    rw [Pi.add_apply, hg j hj, hg' j hj, add_zero]
  rw [cv_eq_sum f (g + g') m hs k N hN, cv_eq_sum f g m hg k N hN,
    cv_eq_sum f g' m hg' k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.add_apply, smul_add]

theorem cv_map {M' : Type} [AddCommGroup M'] [Module R M'] (L : M →ₗ[R] M') (f : PowerSeries R) (g : ℤ → M)
    (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) : L (cv f g k) = cv f (fun k => L (g k)) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [cv_eq_sum f g m hg k N hN,
    cv_eq_sum f (fun j => L (g j)) m (fun j hj => by rw [hg j hj, map_zero]) k N hN,
    map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]

theorem cv_mul (f f' : PowerSeries R) (g : ℤ → M) (m : ℤ) (hg : ∀ k < m, g k = 0) (k : ℤ) :
    cv (f * f') g k = cv f (cv f' g) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  have hc : ∀ j < m, cv f' g j = 0 := fun j hj => cv_low f' g m hg j hj
  rw [cv_eq_sum (f * f') g m hg k N hN, cv_eq_sum f (cv f' g) m hc k N hN]
  have inner : ∀ a ∈ Finset.range N, coeff a f • cv f' g (k - a) =
      ∑ b ∈ Finset.range (N - a), coeff a f • coeff b f' • g (k - a - b) := by
    intro a _
    rw [cv_eq_sum f' g m hg (k - a) N (by omega), Finset.smul_sum]
    symm
    apply Finset.sum_subset (fun x hx => Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.sub_le N a)))
    intro b _ hb
    rw [Finset.mem_range] at hb
    rw [hg (k - a - b) (by omega), smul_zero, smul_zero]
  calc ∑ j ∈ Finset.range N, coeff j (f * f') • g (k - j)
      = ∑ j ∈ Finset.range N, ∑ a ∈ Finset.range (j + 1),
          coeff a f • coeff (j - a) f' • g (k - a - ((j - a : ℕ) : ℤ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [PowerSeries.coeff_mul, Finset.sum_smul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => (coeff a f * coeff b f') • g (k - j)) j]
        refine Finset.sum_congr rfl fun a ha => ?_
        have ha' := Finset.mem_range.mp ha
        rw [mul_smul, show k - (a : ℤ) - ((j - a : ℕ) : ℤ) = k - j by omega]
    _ = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range (N - a),
          coeff a f • coeff b f' • g (k - a - b) :=
        Finset.sum_range_diag_flip N (fun a b => coeff a f • coeff b f' • g (k - a - b))
    _ = ∑ a ∈ Finset.range N, coeff a f • cv f' g (k - a) :=
        (Finset.sum_congr rfl inner).symm

end Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

namespace Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt

open PowerSeries

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

theorem cv_twist (L : M →ₗ[R] M) (c : R) (hc : c ≠ 0) (f : PowerSeries R) (g : ℤ → M) (m : ℤ)
    (hg : ∀ k < m, g k = 0) (k : ℤ) :
    c ^ k • L (cv f g k) = cv (rescale c f) (fun k => c ^ k • L (g k)) k := by
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  have hL : ∀ j < m, c ^ j • L (g j) = 0 := fun j hj => by rw [hg j hj, map_zero, smul_zero]
  rw [cv_map L f g m hg k,
    cv_eq_sum f (fun j => L (g j)) m (fun j hj => by rw [hg j hj, map_zero]) k N hN,
    cv_eq_sum (rescale c f) (fun j => c ^ j • L (g j)) m hL k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  have hp : c ^ j * c ^ (k - (j : ℤ)) = c ^ k := by
    rw [← zpow_natCast, ← zpow_add₀ hc]
    congr 1
    ring
  rw [← hp]
  ring

end Formalism.MainNotions.N.Ln03.Pf.ConvolutionAlt
