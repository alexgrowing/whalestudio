import Mathlib

noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac

structure JSetup (K : Type*) [Field K] where
  σ : K →+* K
  O : Subring K
  p : K
  hp0 : p ≠ 0
  hpO : p ∈ O
  hσp : σ p = p
  hσO : ∀ x ∈ O, σ x ∈ O
  hσσ : ∀ x ∈ O, σ (σ x) = x
  hinv : ∀ x ∈ O, (¬ ∃ y ∈ O, x = p * y) → x⁻¹ ∈ O
  hone : ¬ ∃ y ∈ O, (1 : K) = p * y
  htwo : (2 : K)⁻¹ ∈ O
  h2 : (2 : K) ≠ 0
  hnorm : ∀ u ∈ O, σ u = u → (¬ ∃ y ∈ O, u = p * y) → ∃ w ∈ O, σ w * w = u
  hsep : ∀ x ∈ O, x ≠ 0 → ∃ N : ℕ, ¬ ∃ y ∈ O, x = p ^ N * y

variable {K : Type*} [Field K] (S : JSetup K)

namespace JSetup

def NU (x : K) : Prop := ∃ y ∈ S.O, x = S.p * y

theorem NU_zero : S.NU 0 := ⟨0, S.O.zero_mem, by rw [mul_zero]⟩

theorem NU_add {x y : K} (hx : S.NU x) (hy : S.NU y) : S.NU (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, S.O.add_mem ha hb, by rw [mul_add]⟩

theorem NU_neg {x : K} (hx : S.NU x) : S.NU (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, S.O.neg_mem ha, by rw [mul_neg]⟩

theorem NU_mul {x z : K} (hz : z ∈ S.O) (hx : S.NU x) : S.NU (z * x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨z * a, S.O.mul_mem hz ha, by ring⟩

theorem NU_sum {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, S.NU (f i)) : S.NU (∑ i ∈ s, f i) := by
  exact Finset.sum_induction _ S.NU (fun _ _ => S.NU_add) S.NU_zero h

theorem ne_zero_of_not_NU {x : K} (hx : ¬ S.NU x) : x ≠ 0 := by
  rintro rfl
  exact hx S.NU_zero

theorem NU_σ {x : K} (hx : S.NU x) : S.NU (S.σ x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨S.σ a, S.hσO a ha, by rw [map_mul, S.hσp]⟩

theorem not_NU_σ {x : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) : ¬ S.NU (S.σ x) := by
  intro h
  apply hx
  have h2 := S.NU_σ h
  rwa [S.hσσ x hxO] at h2

theorem not_NU_inv {x : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) : ¬ S.NU x⁻¹ := by
  have hx0 : x ≠ 0 := S.ne_zero_of_not_NU hx
  rintro ⟨a, ha, hxa⟩
  apply S.hone
  refine ⟨x * a, S.O.mul_mem hxO ha, ?_⟩
  calc (1 : K) = x * x⁻¹ := (mul_inv_cancel₀ hx0).symm
    _ = S.p * (x * a) := by rw [hxa]; ring

theorem NU_of_mul {x y : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) (h : S.NU (x * y)) : S.NU y := by
  have hx0 : x ≠ 0 := S.ne_zero_of_not_NU hx
  have hxi : x⁻¹ ∈ S.O := S.hinv x hxO hx
  obtain ⟨a, ha, hxa⟩ := h
  refine ⟨x⁻¹ * a, S.O.mul_mem hxi ha, ?_⟩
  calc y = x⁻¹ * (x * y) := by rw [← mul_assoc, inv_mul_cancel₀ hx0, one_mul]
    _ = S.p * (x⁻¹ * a) := by rw [hxa]; ring

theorem not_NU_mul {x y : K} (hxO : x ∈ S.O) (hx : ¬ S.NU x) (hy : ¬ S.NU y) : ¬ S.NU (x * y) :=
  fun h => hy (S.NU_of_mul hxO hx h)

theorem two_mem : (2 : K) ∈ S.O := by
  have h := S.O.add_mem S.O.one_mem S.O.one_mem
  rwa [one_add_one_eq_two] at h

theorem not_NU_two : ¬ S.NU (2 : K) := by
  rintro ⟨a, ha, h2a⟩
  apply S.hone
  refine ⟨(2 : K)⁻¹ * a, S.O.mul_mem S.htwo ha, ?_⟩
  calc (1 : K) = (2 : K)⁻¹ * 2 := (inv_mul_cancel₀ S.h2).symm
    _ = S.p * ((2 : K)⁻¹ * a) := by rw [h2a]; ring

theorem not_NU_add {x y : K} (hx : ¬ S.NU x) (hy : S.NU y) : ¬ S.NU (x + y) := by
  intro h
  apply hx
  have h2 := S.NU_add h (S.NU_neg hy)
  rwa [add_neg_cancel_right] at h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IntV (x : ι → K) : Prop := ∀ i, x i ∈ S.O

def IntM (Γ : Matrix ι ι K) : Prop := ∀ i j, Γ i j ∈ S.O

def cv (x : ι → K) : ι → K := fun i => S.σ (x i)

def Herm (Γ : Matrix ι ι K) : Prop := ∀ i j, S.σ (Γ i j) = Γ j i

def hf (Γ : Matrix ι ι K) (x y : ι → K) : K := S.cv x ⬝ᵥ (Γ *ᵥ y)

def UM (Γ : Matrix ι ι K) : Prop :=
  ∀ x : ι → K, S.IntV x → (∀ i, S.NU ((Γ *ᵥ x) i)) → ∃ x', S.IntV x' ∧ Γ *ᵥ x = S.p • (Γ *ᵥ x')

theorem IntV_mulVec {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x : ι → K} (hx : S.IntV x) : S.IntV (Γ *ᵥ x) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact S.O.sum_mem fun j _ => S.O.mul_mem (hΓ i j) (hx j)

theorem IntV_cv {x : ι → K} (hx : S.IntV x) : S.IntV (S.cv x) := fun i => S.hσO (x i) (hx i)

theorem hf_mem {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) {x y : ι → K} (hx : S.IntV x) (hy : S.IntV y) :
    S.hf Γ x y ∈ S.O := by
  unfold hf
  simp only [dotProduct]
  exact S.O.sum_mem fun i _ => S.O.mul_mem (S.IntV_cv hx i) (S.IntV_mulVec hΓ hy i)

theorem hf_swap {Γ : Matrix ι ι K} (hΓ : S.IntM Γ) (hH : S.Herm Γ) {x y : ι → K} (hx : S.IntV x)
    (hy : S.IntV y) : S.hf Γ y x = S.σ (S.hf Γ x y) := by
  unfold hf cv
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [S.hσσ _ (hx _), hH]
  ring

theorem σ_mulVec {Γ : Matrix ι ι K} (hH : S.Herm Γ) (a : ι → K) (i : ι) :
    S.σ ((Γ *ᵥ a) i) = (S.cv a ᵥ* Γ) i := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv, hH i]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem σ_vecMul {Γ : Matrix ι ι K} (hH : S.Herm Γ) {a : ι → K} (ha : S.IntV a) (j : ι) :
    S.σ ((S.cv a ᵥ* Γ) j) = (Γ *ᵥ a) j := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, cv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.hσσ _ (ha i), hH i j, mul_comm]

end JSetup

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Jac
