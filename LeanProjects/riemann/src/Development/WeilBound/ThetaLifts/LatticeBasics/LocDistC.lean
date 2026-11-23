import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistA

open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] {n d : ℕ}

def blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : Matrix (Fin (d + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons a b) fun i => Fin.cons 0 (h i))

theorem det_blk (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) : (blk a b h).det = a * h.det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have : (blk a b h).submatrix Fin.succ Fin.succ = h := by ext i j; simp [blk]
  simp [blk] at this ⊢
  simp [this]

theorem mul_blk_zero {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m) :
    (X * blk a b h) i 0 = X i 0 * a := by simp [mul_apply, Fin.sum_univ_succ, blk]

theorem mul_blk_succ {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m)
    (j : Fin d) : (X * blk a b h) i j.succ = X i 0 * b j + ∑ s, X i s.succ * h s j := by
  simp [mul_apply, Fin.sum_univ_succ, blk]

theorem blk_comm (a : k) (b b' : Fin d → k) (hb : b = (a - 1) • b') :
    blk a 0 1 * blk 1 b' 1 = blk 1 b 1 * (blk 1 b' 1 * blk a 0 1) := by
  subst hb
  ext i j
  rw [← Matrix.mul_assoc]
  refine Fin.cases ?_ (fun j => ?_) j <;> simp only [mul_blk_zero, mul_blk_succ] <;>
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [blk, one_apply]
  ring

def chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k :=
  ((fun i => X i 0, fun j => X 0 j.succ / X 0 0), Matrix.of fun i j => X i.succ j.succ - X i.succ 0 * (X 0 j.succ / X 0 0))

def chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) : Matrix (Fin (n + 1)) (Fin (d + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons (y.1.1 0) fun j => y.1.1 0 * y.1.2 j)
    fun i => Fin.cons (y.1.1 i.succ) fun j => y.1.1 i.succ * y.1.2 j + y.2 i j)

theorem chR_chE (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) : chR (chE X) = X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR, chE]
  field_simp

theorem chE_chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) (hy : y.1.1 0 ≠ 0) : chE (chR y) = y := by
  obtain ⟨⟨x, u⟩, W⟩ := y
  simp only at hy
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [chR, chE]
  · ext j; simp [chR, chE, hy]
  · ext i j; simp [chR, chE, hy]

theorem chE_unip (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (hX : X 0 0 ≠ 0) (b : Fin d → k) :
    chE (X * blk 1 b 1) = (((chE X).1.1, (chE X).1.2 + b), (chE X).2) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j; simp [chE, mul_blk_zero, mul_blk_succ, one_apply]; field_simp; ring
  · ext i j; simp [chE, mul_blk_zero, mul_blk_succ, one_apply]; field_simp; ring

theorem chE_levi (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (h : Matrix (Fin d) (Fin d) k) :
    chE (X * blk 1 0 h) = (((chE X).1.1, (chE X).1.2 ᵥ* h), (chE X).2 * h) := by
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · ext i; simp [chE, mul_blk_zero]
  · ext j
    simp only [chE, mul_blk_zero, mul_blk_succ, vecMul, dotProduct, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  · ext i j
    simp only [chE, mul_blk_zero, mul_blk_succ, of_apply, Pi.zero_apply, mul_zero, zero_add, mul_one, Finset.sum_div]
    rw [mul_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by simp only [of_apply]; ring

def Deg {m : Type} (X : Matrix m (Fin d) k) : Prop := ∃ v ≠ 0, X *ᵥ v = 0

theorem Deg.chE {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k} (h : Deg X) (hX : X 0 0 ≠ 0) : Deg (chE X).2 := by
  obtain ⟨v, hv, h⟩ := h
  have hi : ∀ i, X i 0 * v 0 + ∑ j : Fin d, X i j.succ * v j.succ = 0 := fun i => by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h i
  refine ⟨fun j => v j.succ, fun h0 => hv ?_, ?_⟩
  · have h1 : ∀ j : Fin d, v j.succ = 0 := congrFun h0
    ext j
    refine Fin.cases ?_ h1 j
    simpa [h1, hX] using hi 0
  · ext i
    have : ∑ j : Fin d, X i.succ 0 * (X 0 j.succ / X 0 0) * v j.succ = X i.succ 0 / X 0 0 * ∑ j : Fin d, X 0 j.succ * v j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    simp only [LD.chE, mulVec, dotProduct, of_apply, sub_mul, Finset.sum_sub_distrib, this, Pi.zero_apply,
      eq_neg_of_add_eq_zero_right (hi 0), eq_neg_of_add_eq_zero_right (hi i.succ)]
    field_simp; ring

variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]

theorem sb_right {m : Type} {φ : Matrix m (Fin d) k → ℂ} (hφ : φ ∈ SB _) {h : Matrix (Fin d) (Fin d) k} (hh : h.det ≠ 0) :
    (fun y => φ (y * h)) ∈ SB (Matrix m (Fin d) k) :=
  sb_comp (· * h) (· * h⁻¹) (by fun_prop) (by fun_prop) (fun x => mul_nonsing_inv_cancel_right h x hh.isUnit) hφ

theorem cont_chE : ContinuousOn (chE (k := k) (n := n) (d := d)) {X | X 0 0 ≠ 0} := by
  have h : ∀ j : Fin d, ContinuousOn (fun X : Matrix (Fin (n + 1)) (Fin (d + 1)) k => X 0 j.succ / X 0 0) {X | X 0 0 ≠ 0} :=
    fun j => ContinuousOn.div (by fun_prop) (by fun_prop) fun _ h => h
  refine ContinuousOn.prodMk (ContinuousOn.prodMk (by fun_prop) (continuousOn_pi.2 h))
    (continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_)
  exact ContinuousOn.sub (by fun_prop) (ContinuousOn.mul (by fun_prop) (h j))

theorem cont_chR : Continuous (chR (k := k) (n := n) (d := d)) := by
  refine continuous_matrix fun i j => ?_
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [chR] <;> fun_prop

theorem sb_chE {F : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k → ℂ} (hF : F ∈ SB _)
    (h0 : ∀ y, y.1.1 0 = 0 → F y = 0) : (fun X => F (chE X)) ∈ SB (Matrix (Fin (n + 1)) (Fin (d + 1)) k) :=
  sb_chart (U := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (T := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const) cont_chE
    cont_chR.continuousOn chR_chE (fun y hy => by simpa [chR] using hy) hF (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun X hX => h0 _ (not_not.1 hX)

theorem sb_chR {φ : Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X 0 0 = 0 → φ X = 0) :
    (fun y => φ (chR y)) ∈ SB (((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) :=
  sb_chart (T := {X : Matrix (Fin (n + 1)) (Fin (d + 1)) k | X 0 0 ≠ 0})
    (U := {y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k | y.1.1 0 ≠ 0}) (isOpen_ne_fun (by fun_prop) continuous_const)
    cont_chR.continuousOn cont_chE chE_chR (fun _ hy => hy) hφ (fun y hy => h0 y (not_not.1 hy))
    (fun _ _ => rfl) fun y hy => h0 _ (by simpa [chR] using hy)

def Eqv (c : k → ℂ) {m : Type} (l : (Matrix m (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ h : Matrix (Fin d) (Fin d) k, h.det ≠ 0 → ∃ t : ℝ, 0 < t ∧ ∀ φ ∈ SB _, l (fun y => φ (y * h)) = c h.det * t * l φ

theorem Eqv.unip {c : k → ℂ} (hc : ∀ a ≠ 0, c a ≠ 0) {ϖ : k} (h0 : ϖ ≠ 0) (h1 : ϖ ≠ 1) {m : Type}
    {l : (Matrix m (Fin (d + 1)) k → ℂ) →ₗ[ℂ] ℂ} [Fintype m] (hl : Eqv c l) (b : Fin d → k) :
    ∀ φ ∈ SB _, l (fun y => φ (y * blk 1 b 1)) = l φ := by
  have hu : ∀ b : Fin d → k, (blk 1 b 1).det ≠ 0 := fun b => by simp [det_blk]
  have hD : (blk ϖ (0 : Fin d → k) 1).det ≠ 0 := by simp [det_blk, h0]
  obtain ⟨t₁, -, e₁⟩ := hl _ (hu b)
  obtain ⟨t₂, p₂, e₂⟩ := hl _ (hu ((ϖ - 1)⁻¹ • b))
  obtain ⟨t₃, p₃, e₃⟩ := hl _ hD
  intro φ hφ
  have a := e₃ _ (sb_right hφ (hu ((ϖ - 1)⁻¹ • b)))
  have a' := e₁ _ (sb_right (sb_right hφ hD) (hu ((ϖ - 1)⁻¹ • b)))
  simp only [Matrix.mul_assoc] at a a'
  rw [blk_comm ϖ b _ (by rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.2 h1), one_smul]), a', e₂ _ hφ] at a
  have a2 := e₂ _ (sb_right hφ hD)
  simp only [Matrix.mul_assoc] at a2
  rw [a2, e₃ _ hφ] at a
  rw [e₁ _ hφ]
  have n2 : c (blk 1 ((ϖ - 1)⁻¹ • b) 1).det * t₂ ≠ 0 := mul_ne_zero (hc _ (hu _)) (by exact_mod_cast p₂.ne')
  have n3 : c (blk ϖ (0 : Fin d → k) 1).det * t₃ ≠ 0 := mul_ne_zero (hc _ hD) (by exact_mod_cast p₃.ne')
  apply mul_left_cancel₀ (mul_ne_zero n2 n3)
  linear_combination a

end GlobalTheory.ThK.Dbl.LD
