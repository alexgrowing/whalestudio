import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem tate_eigenvector_estimate : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l) (u : ℚ_[l]) (y : ℂ_[l]) (z : Om l) (N : ℕ) (e δ : ℝ), Per.σC γ y = algebraMap ℚ_[l] ℂ_[l] u * y → ‖u‖ = 1 → (γ ^ N) z = z → ‖y - (z : ℂ_[l])‖ ≤ e → ‖∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)‖ ≤ δ * ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ → 0 ≤ δ → ‖u ^ N - 1‖ * ‖y‖ ≤ max (‖u - 1‖ * e) (δ * e) := by
  intro l _ γ u y z N e δ hy hu hz he hT hδ
  have hca : ∀ c : ℚ_[l], ((algebraMap ℚ_[l] (Om l) c : Om l) : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] c :=
    fun _ => rfl
  have hn : ∀ c : ℚ_[l], ‖algebraMap ℚ_[l] ℂ_[l] c‖ = ‖c‖ := fun c => by
    rw [← hca, PadicComplex.norm_extends, norm_algebraMap']
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  set U : ℂ_[l] := algebraMap ℚ_[l] ℂ_[l] u with hU
  have hv : ‖γ z - algebraMap ℚ_[l] (Om l) u * z‖ ≤ e := by
    rw [← PadicComplex.norm_extends, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul,
      hca, ← GlobalTheory.RingBasics.σC_coe]
    have h1 : Per.σC γ (z : ℂ_[l]) - U * (z : ℂ_[l])
        = U * (y - (z : ℂ_[l])) + -Per.σC γ (y - (z : ℂ_[l])) := by
      rw [map_sub, hy]; ring
    rw [← hU, h1]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hU, hn, hu, one_mul]; exact he
    · rw [norm_neg, GlobalTheory.RingBasics.norm_σC]; exact he
  have hpow : ∀ i : ℕ, Per.σC (γ ^ i) y = U ^ i * y := by
    intro i
    induction i with
    | zero => simp [GlobalTheory.RingBasics.σC_one]
    | succ i ih =>
      rw [pow_succ, GlobalTheory.RingBasics.σC_mul, hy, map_mul, hU, TateTwist.σC_algebraMap, ← hU, ih]
      ring
  have htel : ∑ i ∈ Finset.range N, (γ ^ i) (γ z) = ∑ i ∈ Finset.range N, (γ ^ i) z := by
    have h := Finset.sum_range_sub (fun i => (γ ^ i) z) N
    rw [Finset.sum_sub_distrib] at h
    simp only [hz, pow_zero, AlgEquiv.one_apply, sub_self, pow_succ, AlgEquiv.mul_apply] at h
    exact sub_eq_zero.1 h
  have hTv : ∑ i ∈ Finset.range N, (γ ^ i) (γ z - algebraMap ℚ_[l] (Om l) u * z)
      = algebraMap ℚ_[l] (Om l) (1 - u) * ∑ i ∈ Finset.range N, (γ ^ i) z := by
    simp only [map_sub, map_mul, AlgEquiv.commutes, Finset.sum_sub_distrib, htel, map_one,
      ← Finset.mul_sum]
    ring
  set S : Om l := ∑ i ∈ Finset.range N, (γ ^ i) z with hS
  have hSc : (S : ℂ_[l]) = ∑ i ∈ Finset.range N, Per.σC (γ ^ i) (z : ℂ_[l]) := by
    simp only [GlobalTheory.RingBasics.σC_coe]
    exact map_sum (UniformSpace.Completion.coeRingHom : Om l →+* ℂ_[l]) _ _
  have hB : ‖(U - 1) * (S : ℂ_[l])‖ ≤ δ * e := by
    have h2 : (U - 1) * (S : ℂ_[l]) = -((algebraMap ℚ_[l] (Om l) (1 - u) * S : Om l) : ℂ_[l]) := by
      rw [UniformSpace.Completion.coe_mul, hca, map_sub, map_one, ← hU]; ring
    rw [h2, norm_neg, PadicComplex.norm_extends, ← hTv]
    exact hT.trans (mul_le_mul_of_nonneg_left hv hδ)
  have hA : ‖∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))‖ ≤ e :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg he0 fun i _ => by
      rw [GlobalTheory.RingBasics.norm_σC]; exact he
  have hmain : algebraMap ℚ_[l] ℂ_[l] (u ^ N - 1) * y
      = (U - 1) * (∑ i ∈ Finset.range N, Per.σC (γ ^ i) (y - (z : ℂ_[l]))) + (U - 1) * (S : ℂ_[l]) := by
    rw [hSc, ← mul_add, ← Finset.sum_add_distrib]
    simp only [map_sub, sub_add_cancel, hpow, map_pow, map_one, ← hU]
    rw [← Finset.sum_mul, ← mul_assoc, mul_geom_sum]
  rw [← hn, ← norm_mul, hmain]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ hB)
  have h3 : ‖U - 1‖ = ‖u - 1‖ := by rw [← hn, map_sub, map_one]
  rw [norm_mul, h3]
  exact mul_le_mul_of_nonneg_left hA (norm_nonneg _)

end GlobalTheory.InertiaEigenvalues
