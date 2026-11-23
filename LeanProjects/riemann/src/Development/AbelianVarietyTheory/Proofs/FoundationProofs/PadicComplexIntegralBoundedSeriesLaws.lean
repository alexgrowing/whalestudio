import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta.SerRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_sub_le_max' (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [norm_neg, ← sub_eq_add_neg] at this

theorem norm_finsum_le {ι : Type*} (F : ι → K) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ᶠ i, F i‖ ≤ B := by
  refine finsum_induction (p := fun x => ‖x‖ ≤ B) (by simpa using hB) (fun x y hx hy => ?_) h
  exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

theorem norm_coeff_mul_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 0)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hg 0)
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hA hB) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hA

theorem norm_coeff_add_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f + g)‖ ≤ max A B := by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_sub_le (f g : PowerSeries K) (A B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ A)
    (hg : ∀ n, ‖PowerSeries.coeff n g‖ ≤ B) (n : ℕ) : ‖PowerSeries.coeff n (f - g)‖ ≤ max A B := by
  rw [map_sub]
  exact (norm_sub_le_max' _ _).trans (max_le_max (hf n) (hg n))

theorem norm_coeff_C_le (c : K) (n : ℕ) : ‖PowerSeries.coeff n (PowerSeries.C c)‖ ≤ ‖c‖ := by
  rw [PowerSeries.coeff_C]
  split_ifs <;> simp

theorem intSer_mul {f g : PowerSeries K} (hf : IntSer f) (hg : IntSer g) : IntSer (f * g) := fun n => by
  simpa using norm_coeff_mul_le f g 1 1 hf hg n

theorem intSer_pow {f : PowerSeries K} (hf : IntSer f) (d : ℕ) : IntSer (f ^ d) := by
  induction d with
  | zero => intro n; simpa using norm_coeff_C_le (1 : K) n
  | succ d ih => rw [pow_succ]; exact intSer_mul ih hf

theorem intSer_inv {f : PowerSeries K} (hf : IntSer f) (h0 : ‖PowerSeries.constantCoeff f‖ = 1) :
    IntSer f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · simp [h0]
    · rw [norm_mul, norm_neg, norm_inv, h0, inv_one, one_mul]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      split_ifs with hx
      · rw [norm_mul]
        exact mul_le_one₀ (hf _) (norm_nonneg _) (ih _ hx)
      · simp

theorem norm_coeff_subst_le (f h : PowerSeries K) (B : ℝ) (hf : ∀ n, ‖PowerSeries.coeff n f‖ ≤ B)
    (hh : IntSer h) (h0 : PowerSeries.constantCoeff h = 0) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries K)‖ ≤ B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 0)
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' h0)]
  refine norm_finsum_le _ hB fun d => ?_
  rw [smul_eq_mul, norm_mul]
  simpa using mul_le_mul (hf d) (intSer_pow hh d n) (norm_nonneg _) hB

theorem series_ring_laws : ∀ (p : ℕ) [Fact p.Prime], (∀ f g : PowerSeries ℂ_[p], IntSer f → IntSer g → IntSer (f + g) ∧ IntSer (f - g) ∧ IntSer (f * g)) ∧ (∀ f g : PowerSeries ℂ_[p], BddSer f → BddSer g → BddSer (f + g) ∧ BddSer (f - g) ∧ BddSer (f * g)) ∧ (∀ c : ℂ_[p], BddSer (PowerSeries.C c) ∧ (‖c‖ ≤ 1 → IntSer (PowerSeries.C c))) ∧ IntSer (PowerSeries.X : PowerSeries ℂ_[p]) ∧ (∀ f : PowerSeries ℂ_[p], IntSer f → ‖PowerSeries.constantCoeff f‖ = 1 → IntSer f⁻¹) ∧ (∀ (f h : PowerSeries ℂ_[p]) (B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ B) → IntSer h → PowerSeries.constantCoeff h = 0 → ∀ n, ‖PowerSeries.coeff n (PowerSeries.subst h f : PowerSeries ℂ_[p])‖ ≤ B) ∧ ∀ (f g : PowerSeries ℂ_[p]) (A B : ℝ), (∀ n, ‖PowerSeries.coeff n f‖ ≤ A) → (∀ n, ‖PowerSeries.coeff n g‖ ≤ B) → ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ A * B := by
  intro p _
  refine ⟨fun f g hf hg => ⟨fun n => ?_, fun n => ?_, intSer_mul hf hg⟩,
    fun f g ⟨A, hf⟩ ⟨B, hg⟩ => ⟨⟨_, norm_coeff_add_le f g A B hf hg⟩, ⟨_, norm_coeff_sub_le f g A B hf hg⟩,
      ⟨_, norm_coeff_mul_le f g A B hf hg⟩⟩,
    fun c => ⟨⟨_, norm_coeff_C_le c⟩, fun hc n => (norm_coeff_C_le c n).trans hc⟩, fun n => ?_,
    fun f => intSer_inv, norm_coeff_subst_le, norm_coeff_mul_le⟩
  · simpa using norm_coeff_add_le f g 1 1 hf hg n
  · simpa using norm_coeff_sub_le f g 1 1 hf hg n
  · rw [PowerSeries.coeff_X]
    split_ifs <;> simp

end GlobalTheory.EvenTheta.SerRing
