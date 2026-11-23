import Formalism.PeriodIntegrals.FlagGramNonneg

noncomputable section

open Matrix PI.FlagGramNonneg

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

section Vec

variable {E : Type} [Field E] [StarRing E] {V : Type} [AddCommGroup V] [Module E V]

def amat (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) : Matrix (Fin r) (Fin r) E :=
  fun a b => hT (e a) (e' b)

def uvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e : Fin r → V) (z' : V) : Fin r → E :=
  fun a => hT (e a) z'

def vvec (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (z : V) (e' : Fin r → V) : Fin r → E :=
  fun b => hT z (e' b)

def sval (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V) : E :=
  hT z z' - vvec hT z e' ⬝ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')

def zt (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z : V) : V :=
  z - ∑ a, star ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) a) • e a

def zt' (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z' : V) : V :=
  z' - ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b • e' b

def yv (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (a : Fin r) : V :=
  e a - ∑ b, (amat hT e e')⁻¹ b a • e' b

theorem sum_mul_comm_mulVec {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ b, w b * A c b = (A *ᵥ w) c := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem sum_mul_vecMul {n : Type} [Fintype n] (A : Matrix n n E) (w : n → E) (c : n) :
    ∑ a, w a * A a c = (w ᵥ* A) c := by
  simp only [Matrix.vecMul, dotProduct]

theorem herm {hT : V →ₗ⋆[E] V →ₗ[E] E} (hS : hT.IsSymm) (x y : V) : hT x y = star (hT y x) := by
  first
    | exact (hS.eq y x).symm
    | exact (hS y x).symm

theorem left_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT (z - ∑ a, c a • f a) x = hT z x - ∑ a, star (c a) * hT (f a) x := by
  simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.map_smulₛₗ₂, smul_eq_mul, starRingEnd_apply]

theorem right_sub_sum (hT : V →ₗ⋆[E] V →ₗ[E] E) {ι : Type} [Fintype ι] (z : V) (c : ι → E)
    (f : ι → V) (x : V) :
    hT x (z - ∑ a, c a • f a) = hT x z - ∑ a, c a * hT x (f a) := by
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]

variable (hT : V →ₗ⋆[E] V →ₗ[E] E) {r : ℕ} (e e' : Fin r → V) (z z' : V)

theorem e_zt' (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (e c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum]
  have h : ∑ b, ((amat hT e e')⁻¹ *ᵥ uvec hT e z') b * hT (e c) (e' b) =
      (amat hT e e' *ᵥ ((amat hT e e')⁻¹ *ᵥ uvec hT e z')) c :=
    sum_mul_comm_mulVec (amat hT e e') _ c
  rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA, Matrix.one_mulVec]
  simp [uvec]

theorem zt_e' (hA : IsUnit (amat hT e e').det) (c : Fin r) : hT (zt hT e e' z) (e' c) = 0 := by
  unfold zt
  rw [left_sub_sum]
  simp only [star_star]
  have h : ∑ a, (vvec hT z e' ᵥ* (amat hT e e')⁻¹) a * hT (e a) (e' c) =
      ((vvec hT z e' ᵥ* (amat hT e e')⁻¹) ᵥ* amat hT e e') c :=
    sum_mul_vecMul (amat hT e e') _ c
  rw [h, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hA, Matrix.vecMul_one]
  simp [vvec]

theorem e_zt (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) (c : Fin r) :
    hT (e c) (zt hT e e' z) = 0 := by
  unfold zt
  rw [right_sub_sum, hez]
  simp [he]

theorem e'_zt' (he' : ∀ a b, hT (e' a) (e' b) = 0) (hez' : ∀ a, hT (e' a) z' = 0) (c : Fin r) :
    hT (e' c) (zt' hT e e' z') = 0 := by
  unfold zt'
  rw [right_sub_sum, hez']
  simp [he']

theorem zt_zt (hS : hT.IsSymm) (he : ∀ a b, hT (e a) (e b) = 0) (hez : ∀ a, hT (e a) z = 0) :
    hT (zt hT e e' z) (zt hT e e' z) = hT z z := by
  nth_rw 1 [zt]
  rw [left_sub_sum]
  simp only [e_zt hT e e' z he hez, mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z (e a) = 0 := fun a => by rw [herm hS, hez, star_zero]
  unfold zt
  rw [right_sub_sum]
  simp [hze]

theorem zt'_zt' (hS : hT.IsSymm) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) :
    hT (zt' hT e e' z') (zt' hT e e' z') = hT z' z' := by
  nth_rw 1 [zt']
  rw [left_sub_sum]
  simp only [e'_zt' hT e e' z' he' hez', mul_zero, Finset.sum_const_zero, sub_zero]
  have hze : ∀ a, hT z' (e' a) = 0 := fun a => by rw [herm hS, hez', star_zero]
  unfold zt'
  rw [right_sub_sum]
  simp [hze]

theorem zt_zt' (hA : IsUnit (amat hT e e').det) :
    hT (zt hT e e' z) (zt' hT e e' z') = sval hT e e' z z' := by
  rw [zt', right_sub_sum]
  simp only [zt_e' hT e e' z hA, mul_zero, Finset.sum_const_zero, sub_zero]
  rw [zt, left_sub_sum]
  simp only [star_star]
  unfold sval
  rw [Matrix.dotProduct_mulVec]
  simp [dotProduct, uvec]

theorem yv_yv (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (he' : ∀ a b, hT (e' a) (e' b) = 0) (a c : Fin r) :
    hT (yv hT e e' a) (yv hT e e' c) = if a = c then -2 else 0 := by
  have hAA : amat hT e e' * (amat hT e e')⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have key : ∀ a c, ∑ d, hT (e a) (e' d) * (amat hT e e')⁻¹ d c = if a = c then 1 else 0 := by
    intro a c
    have h := congrFun (congrFun hAA a) c
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  have h1 : ∑ d, (amat hT e e')⁻¹ d c * hT (e a) (e' d) = if a = c then 1 else 0 := by
    rw [← key a c]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  have h2 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) = if a = c then 1 else 0 := by
    have h3 : ∑ b, star ((amat hT e e')⁻¹ b a) * hT (e' b) (e c) =
        star (∑ b, hT (e c) (e' b) * (amat hT e e')⁻¹ b a) := by
      rw [star_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', herm hS (e' b) (e c), mul_comm]
    rw [h3, key c a]
    rcases eq_or_ne a c with h | h
    · subst h
      simp
    · simp [h, Ne.symm h]
  unfold yv
  simp only [left_sub_sum, right_sub_sum, he, he', mul_zero, Finset.sum_const_zero, sub_zero, zero_sub]
  rw [h1, h2]
  split_ifs <;> ring

theorem yv_zt (hS : hT.IsSymm) (hA : IsUnit (amat hT e e').det) (he : ∀ a b, hT (e a) (e b) = 0)
    (hez : ∀ a, hT (e a) z = 0) (a : Fin r) : hT (yv hT e e' a) (zt hT e e' z) = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt hT e e' z he hez]
  have h : ∀ b, hT (e' b) (zt hT e e' z) = 0 := fun b => by
    rw [herm hS, zt_e' hT e e' z hA, star_zero]
  simp [h]

theorem yv_zt' (hA : IsUnit (amat hT e e').det) (he' : ∀ a b, hT (e' a) (e' b) = 0)
    (hez' : ∀ a, hT (e' a) z' = 0) (a : Fin r) : hT (yv hT e e' a) (zt' hT e e' z') = 0 := by
  unfold yv
  rw [left_sub_sum, e_zt' hT e e' z' hA]
  simp [e'_zt' hT e e' z' he' hez']

end Vec

end PI.UnitaryGroupMassFormula.FlagGramNonneg
