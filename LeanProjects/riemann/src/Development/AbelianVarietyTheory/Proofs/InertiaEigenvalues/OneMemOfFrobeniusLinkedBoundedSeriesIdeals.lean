import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddOfMemLdivSet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveGeneratorBoundedMultipleSetStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormConstantCoeffEqOneOfEisensteinFrobeniusCycleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralInversePowerSeriesOfUnitConstantCoStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BK.GcdCore

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem powerSeries_coeff_norm_le_one_mul {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ 1 := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    zero_le_one zero_le_one (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

theorem powerSeries_coeff_norm_le_one_add {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f + g)‖ ≤ 1 := by
  rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem powerSeries_coeff_norm_le_one_pow {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (m : ℕ) : ∀ n, ‖coeff n (f ^ m)‖ ≤ 1 := by
  induction m with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih => intro n; rw [pow_succ]; exact powerSeries_coeff_norm_le_one_mul ih hf n

theorem powerSeries_coeff_norm_le_one_X_pow (i : ℕ) : ∀ n, ‖coeff n ((X : K⟦X⟧) ^ i)‖ ≤ 1 := by
  intro n; rw [coeff_X_pow]; split_ifs <;> simp

theorem powerSeries_coeff_norm_le_one_frobeniusExpand (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) :
    ∀ n, ‖coeff n (frob K l f)‖ ≤ 1 := by
  intro n; rw [coeff_frob]; split_ifs
  · exact hf _
  · simp

theorem coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (l e : ℕ) (hl : ‖(l : K)‖ < 1) : ∀ n, ‖coeff n (E K l e)‖ ≤ 1 := by
  intro n
  rw [E, ← map_natCast (C : K →+* K⟦X⟧)]
  refine powerSeries_coeff_norm_le_one_add (powerSeries_coeff_norm_le_one_X_pow e) (fun m => ?_) n
  rw [coeff_C]; split_ifs
  · exact hl.le
  · simp

theorem powerSeries_coeff_norm_le_one_finset_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (hf : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ 1) :
    ∀ n, ‖coeff n (∑ i ∈ s, f i)‖ ≤ 1 :=
  Finset.sum_induction f (fun g => ∀ n, ‖coeff n g‖ ≤ 1) (fun _ _ ha hb => powerSeries_coeff_norm_le_one_add ha hb)
    (fun n => by simp) hf

theorem sum_X_pow_mul_frob_frobSlice (l : ℕ) [Fact l.Prime] (z : K⟦X⟧) :
    z = ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (frobSlice l i z) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [map_sum]
  simp_rw [coeff_X_pow_mul', coeff_frob, coeff_frobSlice]
  rw [Finset.sum_eq_single (n % l)]
  · have h1 : n % l ≤ n := Nat.mod_le n l
    have h2 : l ∣ n - n % l := Nat.dvd_sub_mod n
    rw [if_pos h1, if_pos h2, Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro i hi hne
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      have hn : n = i + l * c := by omega
      apply hne
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_range.2 (Nat.mod_lt n hl)) h

theorem one_mem_of_frobenius_stable_ideals_boundedPowerSeries (GEN : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) → (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) → (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧ ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q)
  (CYCLE : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1)
  (UNITA : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1) :
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  intro K _ _ _ l e a M₁ M₂ _ _ he hl0 hl1 J hadd hmul _ hprim hphi hsl
  choose Δ hΔJ hΔ1 hΔp hΔdiv using fun τ => GEN K (J τ) (hadd τ) (hmul τ) (hprim τ)
  have hE := coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (K := K) l e hl1

  have hk : ∀ τ, ∃ k : K⟦X⟧, (∀ n, ‖coeff n k‖ ≤ 1) ∧
      Δ τ * k = E K l e ^ M₁ * frob K l (Δ (τ - 1)) := by
    intro τ
    obtain ⟨q, hq1, hq⟩ := hΔdiv τ _ (hphi τ _ (hΔJ (τ - 1)))
      (powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₁) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hΔ1 (τ - 1))))
    exact ⟨q, hq1, hq.symm⟩
  choose k hk1 hk using hk

  have hm : ∀ τ i, ∃ m : K⟦X⟧, i < l → (∀ n, ‖coeff n m‖ ≤ 1) ∧
      frobSlice l i (E K l e ^ M₂ * Δ τ) = Δ (τ - 1) * m := by
    intro τ i
    by_cases hi : i < l
    · have hs1 : ∀ n, ‖coeff n (frobSlice l i (E K l e ^ M₂ * Δ τ))‖ ≤ 1 := fun n => by
        rw [coeff_frobSlice]; exact powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₂) (hΔ1 τ) _
      obtain ⟨q, hq1, hq⟩ := hΔdiv (τ - 1) _ (hsl τ _ (hΔJ τ) i hi) hs1
      exact ⟨q, fun _ => ⟨hq1, hq⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose m hm using hm
  set k' : ZMod a → K⟦X⟧ := fun τ => ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (m τ i) with hk'def
  have hk'1 : ∀ τ n, ‖coeff n (k' τ)‖ ≤ 1 := fun τ =>
    powerSeries_coeff_norm_le_one_finset_sum _ _ fun i hi => powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_X_pow i) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hm τ i (Finset.mem_range.1 hi)).1)
  have hk' : ∀ τ, E K l e ^ M₂ * Δ τ = frob K l (Δ (τ - 1)) * k' τ := by
    intro τ
    rw [sum_X_pow_mul_frob_frobSlice (K := K) l (E K l e ^ M₂ * Δ τ), hk'def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hm τ i (Finset.mem_range.1 hi)).2, map_mul]
    ring
  have hne : ∀ τ, Δ τ ≠ 0 := fun τ h => by
    obtain ⟨n, hn⟩ := hΔp τ
    rw [h, map_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hkk : ∀ τ, k τ * k' τ = E K l e ^ (M₁ + M₂) := by
    intro τ
    apply mul_left_cancel₀ (hne τ)
    calc Δ τ * (k τ * k' τ) = E K l e ^ M₁ * (frob K l (Δ (τ - 1)) * k' τ) := by
          rw [← mul_assoc, hk τ, mul_assoc]
      _ = Δ τ * E K l e ^ (M₁ + M₂) := by rw [← hk' τ, pow_add]; ring
  have hc := CYCLE K l e a M₁ (M₁ + M₂) he hl0 hl1 Δ k k' hΔ1 hΔp hk1 hk'1 hkk hk
  intro τ
  obtain ⟨g, hg1, hg⟩ := UNITA K (Δ τ) (hΔ1 τ) (hc τ)
  have := hmul τ _ (hΔJ τ) g ⟨1, hg1⟩
  rwa [mul_comm, hg] at this

theorem one_mem : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ :=
  one_mem_of_frobenius_stable_ideals_boundedPowerSeries GlobalTheory.T.exists_primitive_generator_boundedMultiple_set GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle GlobalTheory.T.exists_integral_inverse_powerSeries_of_unit_constantCoeff

end GlobalTheory.BK.GcdCore
