import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandSeriesShiftIdentityStatement
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.ValPhi

open PowerSeries

section
variable {A : Type} [Ring A] (N : A) (τ : ℕ → A)

theorem bco_of_lt : ∀ (m j : ℕ), m < j → bco N τ m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j h
    cases j with
    | zero => omega
    | succ j => simp [bco]
  | succ m ih =>
    intro j h
    cases j with
    | zero => omega
    | succ j => rw [bco, ih j (by omega), ih (j + 1) (by omega)]; simp

theorem bco_self (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => simp [bco]
  | succ m ih => rw [bco, ih, bco_of_lt N τ m (m + 1) (by omega)]; simp

theorem eq_phiSeq (p : ℕ → A) (h : ∀ m, ∑ j ∈ range (m + 1), bco N τ m j * p j = τ m) (m : ℕ) :
    p m = phiSeq N τ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have e : ∑ j ∈ range m, bco N τ m j * phiSeq N τ j = ∑ j ∈ range m, bco N τ m j * p j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
    rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m, e, ← h m,
      sum_range_succ, bco_self, one_mul]
    abel
end

section
variable (N : ℂ) (τ : ℕ → ℂ)

noncomputable def bser (j : ℕ) : PowerSeries ℂ := PowerSeries.mk (fun m => bco N τ m j)

theorem coeff_bser (j m : ℕ) : coeff m (bser N τ j) = bco N τ m j := by simp [bser]

theorem constantCoeff_bser (j : ℕ) : constantCoeff (bser N τ j) = bco N τ 0 j := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_bser]

theorem bser_zero : (1 - C N * X) * bser N τ 0 = 1 - X * PowerSeries.mk τ := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul, coeff_one]

theorem bser_succ (j : ℕ) : (1 - C N * X) * bser N τ (j + 1) = X * bser N τ j := by
  have e : ∀ f : PowerSeries ℂ, (1 - C N * X) * f = f - C N * (X * f) := fun f => by ring
  rw [e]
  ext k
  cases k with
  | zero => simp [constantCoeff_bser, bco]
  | succ k =>
    simp [coeff_bser, bco, coeff_succ_X_mul]

theorem bser_eq {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1) (j : ℕ) :
    bser N τ j = (1 - X * PowerSeries.mk τ) * w ^ (j + 1) * X ^ j := by
  induction j with
  | zero =>
    have := bser_zero N τ
    rw [← this]
    linear_combination (-(bser N τ 0)) * hw
  | succ j ih =>
    have := bser_succ N τ j
    rw [ih] at this
    linear_combination (-(bser N τ (j + 1))) * hw + w * this

end

theorem mk_decomp (g : ℕ → ℂ) (m : ℕ) :
    PowerSeries.mk g = ∑ j ∈ range (m + 1), g j • (X : PowerSeries ℂ) ^ j
      + X ^ (m + 1) * PowerSeries.mk (fun i => g (i + (m + 1))) := by
  ext k
  simp only [map_add, map_sum, coeff_mk, coeff_X_pow_mul', LinearMap.map_smul, coeff_X_pow,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hk : m + 1 ≤ k
  · rw [if_pos hk, Nat.sub_add_cancel hk, sum_ite_eq]
    simp [mem_range]
    omega
  · rw [if_neg hk, sum_ite_eq, if_pos (mem_range.2 (by omega))]
    simp

theorem sum_of_subst (N : ℂ) (τ g : ℕ → ℂ) {w : PowerSeries ℂ} (hw : (1 - C N * X) * w = 1)
    (ha : HasSubst (-(X * w)))
    (h : (1 - X * PowerSeries.mk τ) * subst (-(X * w)) (1 - X * PowerSeries.mk g) = 1) (m : ℕ) :
    ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j) = τ m := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  set H := PowerSeries.mk (fun i => g (i + (m + 1))) with hH
  set Q := 1 - X * PowerSeries.mk τ with hQ
  have hG : θ (PowerSeries.mk g) = ∑ j ∈ range (m + 1), g j • (-(X * w)) ^ j
      + (-(X * w)) ^ (m + 1) * θ H := by
    conv_lhs => rw [mk_decomp g m]
    simp only [map_add, map_sum, map_smul, map_mul, map_pow, hX, hH]
  rw [hθ, map_sub, map_one, map_mul, hX, hG] at h
  have hterm : ∀ j, Q * (X * w) * (g j • (-(X * w)) ^ j)
      = (g j * (-1) ^ j) • (X * bser N τ j) := by
    intro j
    rw [bser_eq N τ hw j, neg_pow]
    simp only [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one]
    ring
  have hfin : Q + ∑ j ∈ range (m + 1), (g j * (-1) ^ j) • (X * bser N τ j)
      + X ^ (m + 2) * (Q * w * (-w) ^ (m + 1) * θ H) = 1 := by
    rw [← h, ← sum_congr rfl fun j _ => hterm j, ← mul_sum, neg_mul_eq_mul_neg X w, mul_pow]
    ring
  have hc := congrArg (coeff (m + 1)) hfin
  simp only [map_add, map_sum, LinearMap.map_smul, coeff_succ_X_mul, coeff_bser, coeff_X_pow_mul',
    smul_eq_mul, hQ, map_sub, coeff_mk, coeff_one] at hc
  simp at hc
  have e : ∑ j ∈ range (m + 1), bco N τ m j * ((-1) ^ j * g j)
      = ∑ x ∈ range (m + 1), g x * (-1) ^ x * bco N τ m x :=
    sum_congr rfl fun j _ => by ring
  rw [e]
  linear_combination hc

theorem mul_subst_eq_one (n : ℕ) (cc : Fin n → ℂ) {w : PowerSeries ℂ}
    (hw : (1 - C (n : ℂ) * X) * w = 1) (ha : HasSubst (-(X * w))) :
    (1 - X * gser cc) * subst (-(X * w)) (1 - X * gser (fun a => - cc a)) = 1 := by
  let θ : PowerSeries ℂ →ₐ[ℂ] PowerSeries ℂ := substAlgHom ha
  have hθ : ∀ f, subst (-(X * w)) f = θ f := fun f => by simp [θ, coe_substAlgHom]
  have hX : θ X = -(X * w) := by rw [← hθ]; exact subst_X ha
  have hC : ∀ c : ℂ, θ (C c) = C c := fun c => θ.commutes c
  have e1 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2 + 1) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2) + C (cc i + ((n : ℂ) - 1) / 2 + 1) := by
      rw [← map_add]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have e2 : ∀ i, 1 - C (-cc i + ((n : ℂ) - 1) / 2 + 1) * -(X * w)
      = w * (1 - C (cc i + ((n : ℂ) - 1) / 2) * X) := by
    intro i
    have hn : C (n : ℂ) = C (-cc i + ((n : ℂ) - 1) / 2 + 1) + C (cc i + ((n : ℂ) - 1) / 2) := by
      rw [← map_add]; congr 1; ring
    linear_combination (-1 : PowerSeries ℂ) * hw - X * w * hn
  have h1 := GlobalTheory.T.gelfand_series_shift_identity n cc
  have h2 := congrArg θ (GlobalTheory.T.gelfand_series_shift_identity n (fun a => - cc a))
  simp only [map_mul, map_prod, map_sub, map_one, hC, hX, e1, e2, prod_mul_distrib, prod_const,
    card_univ, Fintype.card_fin] at h2
  set D := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2 + 1) * (X : PowerSeries ℂ)) with hD
  set E := ∏ a, (1 - C (cc a + ((n : ℂ) - 1) / 2) * (X : PowerSeries ℂ)) with hE
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hD0 : D ≠ 0 := by
    refine prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg constantCoeff h0
    simp at this
  rw [hθ, map_sub, map_one, map_mul, hX]
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero n hw0) hD0) ?_
  linear_combination (1 - X * gser cc) * h2 + w ^ n * h1

theorem gelfVal_neg_eq_phiSeq : ∀ (n : ℕ) (cc : Fin n → ℂ) (m : ℕ),
    (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m = phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc) m := by
  intro n cc m
  have hu : constantCoeff (1 - C (n : ℂ) * X : PowerSeries ℂ) ≠ 0 := by simp
  have hw := PowerSeries.mul_inv_cancel _ hu
  have ha : HasSubst (-(X * (1 - C (n : ℂ) * X : PowerSeries ℂ)⁻¹)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  exact eq_phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal cc)
    (fun m => (-1 : ℂ) ^ m * GlobalTheory.Dec.gelfVal (fun a => - cc a) m)
    (sum_of_subst (n : ℂ) _ _ hw ha (mul_subst_eq_one n cc hw ha)) m

end GlobalTheory.CompanionTheory.WaveMult.ValPhi
