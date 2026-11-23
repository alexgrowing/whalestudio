import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PadicMvPowerSeriesExt

theorem eq_zero_of_forall_pow_dvd (p : ℕ) (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (A : Type) [CommRing A] [Algebra O A]
    [Module.Projective O A] (x : A) (hx : ∀ m : ℕ, (p : A) ^ m ∣ x) : x = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O A)
  have h0 : s x = 0 := by
    ext a
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : O)}) O) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    obtain ⟨y, hy⟩ := hx n
    have hxy : x = ((p : O) ^ n) • y := by
      rw [Algebra.smul_def, map_pow, map_natCast, hy]
    rw [hxy, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h1 := LinearMap.congr_fun hs x
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at h1
  exact h1.symm

theorem algHom_ext : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] (F F' : MvPowerSeries σ O →ₐ[O] A), (∀ i, F (X i) = F' (X i)) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F f) → (∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ F' f) → F = F' := by
  classical
  intro p O _ _ σ _ A _ _ _ _ F F' hX hF hF'
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_pow_dvd p O A _ fun m => ?_
  obtain ⟨N₁, hN₁⟩ := hF m
  obtain ⟨N₂, hN₂⟩ := hF' m
  set g := MvPowerSeries.trunc' O (Finsupp.equivFunOnFinite.symm fun _ : σ => max N₁ N₂) f with hg
  have hpoly : F.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      F'.comp (MvPolynomial.coeToMvPowerSeries.algHom O) :=
    MvPolynomial.algHom_ext fun i => by simpa using hX i
  have hg' : F (g : MvPowerSeries σ O) = F' (g : MvPowerSeries σ O) := by
    simpa using DFunLike.congr_fun hpoly g
  have hlow : ∀ α : σ →₀ ℕ, α.degree < max N₁ N₂ →
      MvPowerSeries.coeff α (f - (g : MvPowerSeries σ O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hg, MvPowerSeries.coeff_trunc', if_pos, sub_self]
    intro i
    exact (Finsupp.le_degree i α).trans (by simpa using hα.le)
  have hdiff : F f - F' f = F (f - (g : MvPowerSeries σ O)) - F' (f - (g : MvPowerSeries σ O)) := by
    rw [map_sub, map_sub, hg']
    ring
  rw [hdiff]
  exact dvd_sub (hN₁ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_left _ _)))
    (hN₂ _ fun α h => hlow α (lt_of_lt_of_le h (le_max_right _ _)))

end GlobalTheory.PadicMvPowerSeriesExt
