import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDensityMult

theorem re_lt_one_of_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra hc
  push Not at hc
  by_cases h1 : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    rw [LFunction_modOne_eq] at h
    exact riemannZeta_ne_zero_of_one_le_re hc h
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hc h

theorem log_le {Q N t : ℝ} (hQ : 3 ≤ Q) (hN0 : 0 < N) (hN : N ≤ Q) (ht : |t| ≤ Q + 1) :
    Real.log (N * (|t| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
  have h0 := abs_nonneg t
  have h1 : N * (|t| + 2) ≤ Q ^ 3 := by
    have : N * (|t| + 2) ≤ Q * (Q + 3) := mul_le_mul hN (by linarith) (by linarith) (by linarith)
    have h4 : Q + 3 ≤ Q ^ 2 := by nlinarith
    have h5 : Q * (Q + 3) ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
    have h6 : Q * Q ^ 2 = Q ^ 3 := by ring
    linarith
  have h2 : Real.log (N * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log (by positivity) h1
  have h3 := Real.log_le_rpow_div (x := Q) (ε := (1 : ℝ) / 8) (by linarith) (by norm_num)
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem zero_density_mult : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le
  refine ⟨C₂ * (C₁ * 24), by positivity, ?_⟩
  intro Q hQ T hT
  have hQ0 : 0 < Q := by linarith
  have hcard := H₂ Q hQ T hT
  set g : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hg
  rw [← Finset.coe_image, Set.ncard_coe_finset] at hcard
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  have hcell : ∀ c ∈ T.image g, ∑ p ∈ T with g p = c,
      ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C₁ * (24 * Q ^ ((1 : ℝ) / 8)) := by
    intro c hc
    obtain ⟨⟨n, χ, z⟩, hz, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a1, a2, -, -, a5⟩ := hT _ hz
    simp only at a1 a2 a5
    obtain ⟨hfin, hsum⟩ := H₁ (n + 1) χ a2 (⌊z.im⌋ : ℤ)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hl : Real.log (((n + 1 : ℕ) : ℝ) * (|((⌊z.im⌋ : ℤ) : ℝ)| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
      refine log_le hQ (by positivity) a1 ?_
      have b1 := Int.floor_le z.im
      have b2 := Int.lt_floor_add_one z.im
      rw [abs_le] at a5 ⊢
      constructor <;> linarith [a5.1, a5.2]
    refine le_trans ?_ (hsum.trans (mul_le_mul_of_nonneg_left hl hC₁.le))
    have hinj : Function.Injective
        (fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) := by
      intro x y h
      simpa using h
    have e := Finset.sum_image (s := hfin.toFinset)
      (g := fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))
      (f := fun p => ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ)) hinj.injOn
    refine le_trans ?_ e.le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
    rintro ⟨m, ψ, ρ⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hgp⟩ := hp
    obtain ⟨-, b2, b3, b4, -⟩ := hT _ hp
    simp only [hg] at hgp b2 b3 b4
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hgp
    have h3 := eq_of_heq h2
    obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
    refine Finset.mem_image.2 ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨by linarith, re_lt_one_of_zero _ b2 b3, ?_, b3⟩
    have c1 := Int.floor_le ρ.im
    have c2 := Int.lt_floor_add_one ρ.im
    rw [← h4, abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_card_nsmul _ _ _ hcell).trans ?_
  rw [nsmul_eq_mul]
  have hp : Q ^ ((1 : ℝ) / 4) = Q ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hQ0]; norm_num
  rw [hp]
  calc _ ≤ (C₂ * Q ^ ((1 : ℝ) / 8)) * (C₁ * (24 * Q ^ ((1 : ℝ) / 8))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GlobalTheory.ZeroDensityMult
