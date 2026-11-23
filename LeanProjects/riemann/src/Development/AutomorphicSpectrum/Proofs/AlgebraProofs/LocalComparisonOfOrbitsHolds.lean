import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoSeriesThreeStep

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem orbit_map_pow {A B : Type} (e : A → B) (a : Equiv.Perm A) (b : Equiv.Perm B)
    (he : ∀ t, e (a t) = b (e t)) (n : ℕ) (t : A) : e ((a ^ n) t) = (b ^ n) (e t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, he, ih]

theorem local_comparison_of_orbits : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Sg : Type) [Fintype Sg] [DecidableEq Sg] (P : Ideal (MRing ι O)) (d p : ℕ), 2 ≤ p → ∀ (φ : Equiv.Perm Sg) (r s : Sg → ℕ) (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ))), (∀ τ, ∃ (Sg' : Type) (_ : Finite Sg') (e : Sg' → Sg) (φ' : Equiv.Perm Sg'), τ ∈ Set.range e ∧ (∀ t, e (φ' t) = φ (e t)) ∧ Relations (r := fun t => r (e t)) (s := fun t => s (e t)) P d p φ' (fun t => lie (e t)) (fun t => om (e t))) → LabelChernComparison P d p φ lie om := by
  intro O _ _ _ K _ _ ι _ Sg _ _ P d p hp φ r s lie om hrel k hk Q hQ τ
  obtain ⟨Sg', hfin, e, φ', ⟨t0, ht0⟩, hcomm, hR⟩ := hrel τ
  subst ht0
  haveI : Fintype Sg' := Fintype.ofFinite Sg'
  obtain ⟨h, h1, h2⟩ := hR k hk Q hQ
  obtain ⟨La, hLa⟩ : ∃ La : Sg → ℝ, La = fun σ => ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := ⟨_, rfl⟩
  have hLa' : ∀ σ, La σ = ((laNum P (p : O) (lie σ).x k Q : ℤ) : ℝ) := fun σ => by rw [hLa]
  have h1' : ∀ t, (((lie (e t)).ck P k Q : ℤ) : ℝ) + (((om (e t)).ck P k Q : ℤ) : ℝ)
      = h t - ((laNum P (p : O) (lie (e t)).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1) := fun t => h1 t
  have h2' : ∀ t, (p : ℝ) ^ k * h t = h (φ' t) + La (e (φ' t)) := by
    intro t
    rw [hLa']
    exact h2 t
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hpk : (1 : ℝ) < (p : ℝ) ^ k := one_lt_pow₀ hp1 (by omega)
  have hpk0 : (p : ℝ) ^ k ≠ 0 := (zero_lt_one.trans hpk).ne'
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ((p : ℝ) ^ k)⁻¹ := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact inv_nonneg.mpr (zero_lt_one.trans hpk).le
  have hc1 : c < 1 := by
    rw [hc]
    exact inv_lt_one_of_one_lt₀ hpk
  have hrec : ∀ t, h t = c * (h (φ' t) + La (e (φ' t))) := by
    intro t
    rw [hc, ← h2' t, ← mul_assoc, inv_mul_cancel₀ hpk0, one_mul]
  have hpart : ∀ N t, h t = (∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t)))
      + c ^ N * h ((φ' ^ N) t) := by
    intro N
    induction N with
    | zero => intro t; simp
    | succ N ih =>
      intro t
      have hstep : φ' ((φ' ^ N) t) = (φ' ^ (N + 1)) t := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [ih t, Finset.sum_range_succ, hrec ((φ' ^ N) t), hstep]
      ring
  have hbd : ∀ f : Sg' → ℝ, ∀ t, |f t| ≤ ∑ u, |f u| := fun f t =>
    Finset.single_le_sum (f := fun u => |f u|) (fun u _ => abs_nonneg (f u)) (Finset.mem_univ t)
  have hsum : Summable (fun n : ℕ => c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0))) := by
    have hg : Summable (fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) := by
      refine ((summable_geometric_of_lt_one hc0 hc1).mul_left ((∑ u, |La (e u)|) * c)).congr
        (fun n => ?_)
      ring
    refine Summable.of_norm_bounded (g := fun n : ℕ => (∑ u, |La (e u)|) * c ^ (n + 1)) hg
      (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |La (e u)|)]
    exact mul_le_mul_of_nonneg_left (hbd (fun u => La (e u)) _) (pow_nonneg hc0 _)
  have hlim1 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hz : Filter.Tendsto (fun N : ℕ => c ^ N * h ((φ' ^ N) t0)) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun N : ℕ => (∑ u, |h u|) * c ^ N) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).const_mul (∑ u, |h u|)
      rw [mul_zero] at this
      exact this
    refine squeeze_zero_norm (fun N => ?_) hg
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hc0 _), mul_comm (∑ u, |h u|)]
    exact mul_le_mul_of_nonneg_left (hbd h _) (pow_nonneg hc0 _)
  have hlim2 : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)))
      Filter.atTop (nhds (h t0)) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => h t0) Filter.atTop (nhds (h t0)) := tendsto_const_nhds
    have := hconst.sub hz
    rw [sub_zero] at this
    refine this.congr (fun N => ?_)
    rw [hpart N t0]
    ring
  have hh : h t0 = ∑' n, c ^ (n + 1) * La (e ((φ' ^ (n + 1)) t0)) := tendsto_nhds_unique hlim2 hlim1
  have hh2 : h t0 = ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * La ((φ ^ (n + 1)) (e t0)) := by
    rw [hh, hc]
    refine tsum_congr (fun n => ?_)
    rw [orbit_map_pow e φ' φ hcomm]
  have key := (co_series_three_step).1 Sg φ p k hp hk La (e t0)
  have final : (((lie (e t0)).ck P k Q : ℤ) : ℝ) + (((om (e t0)).ck P k Q : ℤ) : ℝ)
      = ∑ σ, GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (e t0) σ * La σ := by
    rw [key, h1' t0, hh2, hLa' (e t0)]
  subst hLa
  exact final

end GlobalTheory.CompanionTheory.Ar.Num
