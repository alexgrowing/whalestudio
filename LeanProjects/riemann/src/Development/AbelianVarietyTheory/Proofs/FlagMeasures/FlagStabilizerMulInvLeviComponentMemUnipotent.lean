import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

namespace GlobalTheory.LeviUnip

variable {n n₀ a : ℕ} {j : Fin a → ℕ}

theorem umul {ε : Fin n → Bool} (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uone {ε : Fin n → Bool} : uMat (1 : UJ ε) = 1 := rfl

theorem umul_inv {ε : Fin n → Bool} (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by rw [← umul, mul_inv_cancel, uone]

theorem uinv_mul {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by rw [← umul, inv_mul_cancel, uone]

theorem col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {i : Fin a} (hi : i.castSucc < k) (u : Fin (j i) → ℂ) :
    B i *ᵥ u ∈ W k := by
  classical
  refine (hB k _).2 ⟨Pi.single i u, fun i' hi' => ?_, ?_⟩
  · have hne : i' ≠ i := by rintro rfl; exact hi' hi
    exact Pi.single_eq_of_ne hne _
  · rw [Finset.sum_eq_single i (fun b _ hb => by rw [Pi.single_eq_of_ne hb, Matrix.mulVec_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem map_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} (F : Matrix (Fin n) (Fin n) ℂ) (U : Submodule ℂ (Fin n → ℂ))
    (h : ∀ i : Fin a, i.castSucc < k → ∀ u, (F * B i) *ᵥ u ∈ U) {y : Fin n → ℂ} (hy : y ∈ W k) :
    F *ᵥ y ∈ U := by
  obtain ⟨u, hu, rfl⟩ := (hB k y).1 hy
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : i.castSucc < k
  · rw [Matrix.mulVec_mulVec]
    exact h i hi (u i)
  · rw [hu i hi, Matrix.mulVec_zero, Matrix.mulVec_zero]
    exact U.zero_mem

theorem sum_col_mem {B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ} {W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)}
    (hB : SpansFlag B W) {k : Fin (a + 1)} {r : ℕ} (q : ∀ i, Matrix (Fin (j i)) (Fin r) ℂ)
    (hq : ∀ i : Fin a, ¬ i.castSucc < k → q i = 0) (u : Fin r → ℂ) : (∑ i, B i * q i) *ᵥ u ∈ W k := by
  rw [Matrix.sum_mulVec]
  refine (hB k _).2 ⟨fun i => q i *ᵥ u, fun i hi => by
    show q i *ᵥ u = 0
    rw [hq i hi, Matrix.zero_mulVec], ?_⟩
  exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem mul_inv_mem_flagN (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (hF : IsFrame ε ε₀ B B₀)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ)
    (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ) (s h : Formalism.REAL.UJ ε₀)
    (y : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g m : Formalism.REAL.UJ ε)
    (hA : SpansFlag A W) (hB : SpansFlag B W) (hp : ∀ k i, i < k → p k i = 0) (hpd : ∀ i, (p i i).det ≠ 0)
    (hAB : ∀ i, A i = ∑ k, B k * p k i) (hA₀ : A₀ = B₀ * uMat s + ∑ k, B k * d k)
    (hy : ∀ i, (y i).det ≠ 0) (hg : ∀ i, uMat g * A i = A i * y i) (hg₀ : uMat g * A₀ = A₀ * uMat h)
    (hm : uMat m = lev ε B B₀ (fun i => p i i * y i * (p i i)⁻¹) (uMat (s * h * s⁻¹))) :
    g * m⁻¹ ∈ flagN ε W := by
  classical
  have hpu : ∀ i, IsUnit (p i i).det := fun i => isUnit_iff_ne_zero.2 (hpd i)
  have hyu : ∀ i, IsUnit (y i).det := fun i => isUnit_iff_ne_zero.2 (hy i)
  set x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ := fun i => p i i * y i * (p i i)⁻¹ with hx
  have hxu : ∀ i, IsUnit (x i).det := by
    intro i
    rw [isUnit_iff_ne_zero]
    simp [hx, Matrix.det_mul, Matrix.det_nonsing_inv, hpd i, hy i]

  have hMB : ∀ i, uMat m⁻¹ * B i = B i * (x i)⁻¹ := by
    intro i
    have h1 : uMat m * B i = B i * x i := by
      rw [hm]
      exact GlobalTheory.LeviIso.IsFrame.lev_mul_B _ _ hF i
    calc uMat m⁻¹ * B i = uMat m⁻¹ * (B i * (x i * (x i)⁻¹)) := by
          rw [Matrix.mul_nonsing_inv _ (hxu i), Matrix.mul_one]
      _ = (uMat m⁻¹ * uMat m) * B i * (x i)⁻¹ := by
          rw [← Matrix.mul_assoc (B i), ← h1]
          simp only [Matrix.mul_assoc]
      _ = B i * (x i)⁻¹ := by rw [uinv_mul, Matrix.one_mul]

  have hG : ∀ k (v : Fin n → ℂ), v ∈ W k → uMat g *ᵥ v ∈ W k := fun k v hv =>
    map_mem hA (uMat g) (W k) (fun i hi u => by
      rw [hg i, ← Matrix.mulVec_mulVec]
      exact col_mem hA hi _) hv
  have hsub : ∀ v : Fin n → ℂ, uMat (g * m⁻¹) *ᵥ v - v = (uMat g * uMat m⁻¹ - 1) *ᵥ v := by
    intro v
    rw [umul, Matrix.sub_mulVec, Matrix.one_mulVec]

  have hNA : ∀ l, (uMat g * uMat m⁻¹ - 1) * A l =
      uMat g * ∑ k, B k * ((x k)⁻¹ * p k l - p k l * (y l)⁻¹) := by
    intro l
    have e1 : uMat m⁻¹ * A l = ∑ k, B k * ((x k)⁻¹ * p k l) := by
      rw [hAB l, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.mul_assoc, hMB k, Matrix.mul_assoc]
    have e2 : uMat g * A l * (y l)⁻¹ = A l := by
      rw [hg l, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hyu l), Matrix.mul_one]
    calc (uMat g * uMat m⁻¹ - 1) * A l = uMat g * (uMat m⁻¹ * A l) - A l := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * ∑ k, B k * ((x k)⁻¹ * p k l) - uMat g * A l * (y l)⁻¹ := by rw [e1, e2]
      _ = _ := by
          rw [hAB l]
          simp only [Matrix.mul_sub, Finset.sum_sub_distrib, Matrix.mul_sum, Matrix.sum_mul,
            Matrix.mul_assoc]

  have hq0 : ∀ l k, l ≤ k → (x k)⁻¹ * p k l - p k l * (y l)⁻¹ = 0 := by
    intro l k hlk
    rcases hlk.lt_or_eq with h | rfl
    · rw [hp k l h, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    · have : (x l)⁻¹ * p l l = p l l * (y l)⁻¹ := by
        rw [hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hpu l),
          Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hpu l), Matrix.mul_one]
      rw [this, sub_self]

  have hNB₀ : (uMat g * uMat m⁻¹ - 1) * B₀ =
      (∑ k, B k * d k) * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) := by
    have hinv : (s * h * s⁻¹)⁻¹ = s * h⁻¹ * s⁻¹ := by group
    have e1 : uMat m⁻¹ * B₀ = B₀ * (uMat s * uMat h⁻¹ * uMat s⁻¹) := by
      have h1 : uMat m * B₀ = B₀ * uMat (s * h * s⁻¹) := by
        rw [hm]
        exact GlobalTheory.LeviIso.IsFrame.lev_mul_B₀ _ _ hF
      calc uMat m⁻¹ * B₀ = uMat m⁻¹ * (B₀ * (uMat (s * h * s⁻¹) * uMat (s * h * s⁻¹)⁻¹)) := by
            rw [umul_inv, Matrix.mul_one]
        _ = (uMat m⁻¹ * uMat m) * B₀ * uMat (s * h * s⁻¹)⁻¹ := by
            rw [← Matrix.mul_assoc B₀, ← h1]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [uinv_mul, Matrix.one_mul, hinv, umul, umul]
    have e2 : B₀ * uMat s = A₀ - ∑ k, B k * d k := by
      rw [hA₀]
      abel
    calc (uMat g * uMat m⁻¹ - 1) * B₀ = uMat g * (uMat m⁻¹ * B₀) - B₀ := by
          rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = uMat g * (B₀ * uMat s) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e1]
          simp only [Matrix.mul_assoc]
      _ = (A₀ * uMat h - uMat g * ∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [e2, Matrix.mul_sub, hg₀]
      _ = A₀ * uMat s⁻¹ - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by
          rw [Matrix.sub_mul, Matrix.mul_assoc A₀, ← Matrix.mul_assoc (uMat h), umul_inv h,
            Matrix.one_mul]
      _ = (B₀ * uMat s + ∑ k, B k * d k) * uMat s⁻¹
            - uMat g * (∑ k, B k * d k) * (uMat h⁻¹ * uMat s⁻¹) - B₀ := by rw [← hA₀]
      _ = _ := by
          rw [Matrix.add_mul, Matrix.mul_assoc B₀, umul_inv s, Matrix.mul_one]
          abel
  have hlast : ∀ i : Fin a, i.castSucc < Fin.last a := fun i => Fin.castSucc_lt_last i
  have hD : ∀ z, (∑ k, B k * d k) *ᵥ z ∈ W (Fin.last a) := fun z =>
    sum_col_mem hB d (fun i hi => absurd (hlast i) hi) z
  simp only [flagN, Set.mem_ofPred_eq]
  refine ⟨fun i v hv => ?_, fun v hv => ?_⟩
  · rw [hsub]
    refine map_mem hA _ (W i.castSucc) (fun l hl u => ?_) hv
    rw [hNA l, ← Matrix.mulVec_mulVec]
    refine hG _ _ (sum_col_mem hB (fun k => (x k)⁻¹ * p k l - p k l * (y l)⁻¹) (fun k hk => hq0 l k ?_) u)
    rw [Fin.castSucc_lt_castSucc_iff, not_lt] at hk
    rw [Fin.castSucc_lt_succ_iff] at hl
    exact hl.trans hk
  · rw [hsub]

    have hBJ : ∀ i, (B i)ᴴ *ᵥ (Jm ε *ᵥ v) = 0 := by
      intro i
      funext c
      have hc := hv _ (col_mem hB (hlast i) (Pi.single c 1))
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec] at hc
      simpa using hc
    have hdec : v = (∑ i, B i *ᵥ ((B i)ᴴ *ᵥ v)) + B₀ *ᵥ (B₀ᴴ *ᵥ v) := by
      have hF' := hF
      unfold IsFrame at hF'
      obtain ⟨-, -, -, -, -, -, hsum⟩ := hF'
      have := congrArg (· *ᵥ v) hsum
      simp only [Matrix.one_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hBJ,
        Matrix.mulVec_zero, Finset.sum_const_zero, add_zero] at this
      exact this.symm
    rw [hdec, Matrix.mulVec_add]
    refine add_mem ?_ ?_
    · refine map_mem hB _ (W (Fin.last a)) (fun i _ u => ?_)
        ((hB _ _).2 ⟨_, fun i hi => absurd (hlast i) hi, rfl⟩)
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hMB i, Matrix.sub_mulVec]
      refine sub_mem ?_ (col_mem hB (hlast i) u)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hG _ _ (col_mem hB (hlast i) _)
    · rw [Matrix.mulVec_mulVec, hNB₀, Matrix.sub_mulVec]
      refine sub_mem ?_ ?_
      · rw [← Matrix.mulVec_mulVec]
        exact hD _
      · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        exact hG _ _ (hD _)

end GlobalTheory.LeviUnip
