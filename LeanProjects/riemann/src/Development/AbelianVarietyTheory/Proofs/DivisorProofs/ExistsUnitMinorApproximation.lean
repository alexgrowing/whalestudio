import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.MinorBound

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_det_le_one {m : ℕ} (B : Matrix (Fin m) (Fin m) K) (hB : ∀ i j, ‖B i j‖ ≤ 1) :
    ‖B.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
  · rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hB _ _

theorem norm_prod_sub_prod_le {Idx : Type*} (s : Finset Idx) (x y : Idx → K) {ε : ℝ} (hε : 0 ≤ ε)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) (hxy : ∀ i, ‖x i - y i‖ ≤ ε) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i
        = x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; nlinarith [hx a, ih, norm_nonneg (x a), norm_nonneg (∏ i ∈ s, x i - ∏ i ∈ s, y i)]
    · rw [norm_mul, norm_prod]
      have h1 : ∏ i ∈ s, ‖y i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy i
      nlinarith [hxy a, norm_nonneg (x a - y a), Finset.prod_nonneg fun i (_ : i ∈ s) => norm_nonneg (y i)]

theorem norm_det_sub_det_le {m : ℕ} (B C : Matrix (Fin m) (Fin m) K) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (hC : ∀ i j, ‖C i j‖ ≤ 1) (hBC : ∀ i j, ‖B i j - C i j‖ ≤ ε) :
    ‖B.det - C.det‖ ≤ ε := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun σ _ => ?_
  rw [← smul_sub]
  have := norm_prod_sub_prod_le Finset.univ (fun i => B (σ i) i) (fun i => C (σ i) i) hε
    (fun i => hB _ _) (fun i => hC _ _) (fun i => hBC _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
    exact this

theorem det_mul_expand {m g : ℕ} (M : Matrix (Fin m) (Fin g) K) (A : Matrix (Fin g) (Fin m) K) :
    (M * A).det = ∑ κ : Fin m → Fin g, (∏ i, M i (κ i)) * (Matrix.of fun k j => A (κ k) j).det := by
  classical
  have h1 : (M * A) = fun i => ∑ k, M i k • A k := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_sum
    (fun i k => M i k • A k)
  simp only [AlternatingMap.coe_multilinearMap] at h2
  rw [Matrix.det, h1, h2]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h3 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_smul_univ
    (fun i => M i (f i)) (fun i => A (f i))
  simp only [AlternatingMap.coe_multilinearMap] at h3
  rw [h3, smul_eq_mul]
  rfl

theorem exists_minor_ge (p : ℕ) [hp : Fact p.Prime] (n m g : ℕ) (d : ℂ_[p]) (A Cc : Fin g → Fin m → ℂ_[p])
    (G : Matrix (Fin m) (Fin m) ℂ_[p]) (M : Fin m → Fin g → ℂ_[p]) (hd : d ≠ 0)
    (hCc : ∀ k j, ‖Cc k j‖ ≤ 1) (hCA : ∀ k j, ‖Cc k j - A k j‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hM : ∀ i k, ‖M i k‖ ≤ 1) (hG : ‖G.det‖ = 1) (hrel : ∀ i j, d * G i j = ∑ k, M i k * A k j) :
    ∃ K : Fin m → Fin g, ‖d‖ ^ m ≤ ‖(Matrix.of fun k j => A (K k) j).det‖ ∧
      ‖(Matrix.of fun k j => A (K k) j).det‖ ≤ 1 ∧
      ‖(Matrix.of fun k j => Cc (K k) j).det - (Matrix.of fun k j => A (K k) j).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hε : 0 ≤ (p : ℝ)⁻¹ ^ n := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1)
  have hA : ∀ k j, ‖A k j‖ ≤ 1 := fun k j => by
    have h : A k j = Cc k j + -(Cc k j - A k j) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hCc k j) ?_)
    rw [norm_neg]; exact (hCA k j).trans hε1
  have hdet : d ^ m * G.det = (Matrix.of M * Matrix.of A).det := by
    have h : d • G = Matrix.of M * Matrix.of A := by
      ext i j; simp [Matrix.mul_apply, hrel]
    rw [← h, Matrix.det_smul, Fintype.card_fin]
  rw [det_mul_expand] at hdet
  have hGne : G.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hG; exact zero_ne_one hG
  by_cases hne : Nonempty (Fin m → Fin g)
  · obtain ⟨K0, hK0⟩ := Finite.exists_max (fun κ : Fin m → Fin g => ‖(Matrix.of fun k j => A (κ k) j).det‖)
    refine ⟨K0, ?_, norm_det_le_one _ fun i j => hA _ _,
      norm_det_sub_det_le _ _ hε (fun i j => hCc _ _) (fun i j => hA _ _) (fun i j => hCA _ _)⟩
    have h1 : ‖d‖ ^ m = ‖d ^ m * G.det‖ := by rw [norm_mul, norm_pow, hG, _root_.mul_one]
    rw [h1, hdet]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun κ _ => ?_
    rw [norm_mul, norm_prod]
    have hP : ∏ i, ‖Matrix.of M i (κ i)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hM _ _
    calc (∏ i, ‖Matrix.of M i (κ i)‖) * ‖(Matrix.of fun k j => Matrix.of A (κ k) j).det‖
        ≤ 1 * ‖(Matrix.of fun k j => A (κ k) j).det‖ :=
          mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ _ := by rw [_root_.one_mul]; exact hK0 κ
  · exfalso
    haveI : IsEmpty (Fin m → Fin g) := not_nonempty_iff.mp hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hdet
    exact mul_ne_zero (pow_ne_zero _ hd) hGne hdet

end GlobalTheory.MinorBound
