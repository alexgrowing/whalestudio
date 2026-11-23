import Mathlib
import Formalism.PeriodIntegrals.KerTens

noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.KerTens.W

open Formalism.L2.Th1.H (Sesq matH alphaQ qOf opU Th fixedBy)

def blk {n : Type} {N N' : ℕ} (b : Fin N' × Fin N) : (n → ℂ) →ₗ[ℂ] (n → Fin N' → Fin N → ℂ) where
  toFun x := fun τ i j => if (i, j) = b then x τ else 0
  map_add' x y := by
    funext τ i j
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext τ i j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem blk_apply {n : Type} {N N' : ℕ} (b : Fin N' × Fin N) (x : n → ℂ) (τ : n) (i : Fin N') (j : Fin N) :
    blk b x τ i j = if (i, j) = b then x τ else 0 := rfl

def upd {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t : n → ℂ) :
    n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) = b then t τ else z τ i j

def part {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) : n → ℂ :=
  fun τ => z τ b.1 b.2

def repl {n : Type} {N N' : ℕ} (t0 : n → ℂ) (s : Finset (Fin N' × Fin N)) (z : n → Fin N' → Fin N → ℂ) :
    n → Fin N' → Fin N → ℂ :=
  fun τ i j => if (i, j) ∈ s then t0 τ else z τ i j

theorem upd_eq {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t : n → ℂ) :
    upd z b t = (fun τ i j => if (i, j) = b then 0 else z τ i j) + blk b t := by
  funext τ i j
  simp only [upd, Pi.add_apply, blk_apply]
  split_ifs <;> simp

theorem upd_add {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) (t x : n → ℂ) :
    upd z b t + blk b x = upd z b (t + x) := by
  funext τ i j
  simp only [upd, Pi.add_apply, blk_apply]
  split_ifs <;> simp

theorem upd_part {n : Type} {N N' : ℕ} (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) :
    upd z b (part z b) = z := by
  funext τ i j
  simp only [upd, part]
  split_ifs with h
  · subst h
    rfl
  · rfl

theorem formV_blk (A : ℝ) {n : Type} [Fintype n] {N N' : ℕ} (w : n → Fin N' → Fin N → ℂ)
    (b : Fin N' × Fin N) (x : n → ℂ) :
    formV A n N N' w (blk b x) = (∑ τ, w τ b.1 b.2 * conj (x τ)) / (A : ℂ) := by
  simp only [formV, LinearMap.mk₂'ₛₗ_apply, blk_apply, Prod.ext_iff, ite_and]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq']

theorem matH_hOne (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (t x : n → ℂ) :
    matH (hOne L n) t x = (∑ τ, t τ * conj (x τ)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
  unfold matH hOne
  simp only [LinearMap.mk₂'ₛₗ_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

theorem slice_th (c : ℝ) (L : PeriodPair) {n : Type} [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ))
    {N N' : ℕ} (F : (n → Fin N' → Fin N → ℂ) → ℂ)
    (hF : F ∈ Th (formV (Formalism.L2.Th1.F.area L) n N N') (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N'))
      (powLat ΛM N N'))
    (z : n → Fin N' → Fin N → ℂ) (b : Fin N' × Fin N) :
    (fun t => F (upd z b t)) ∈ Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM := by
  obtain ⟨hFa, hFf⟩ := hF
  have hA : AnalyticOnNhd ℂ (fun t : n → ℂ => upd z b t) Set.univ := by
    intro t _
    rw [show (fun t : n → ℂ => upd z b t) =
        fun t => (fun τ i j => if (i, j) = b then 0 else z τ i j) + blk b t from
      funext fun t => upd_eq z b t]
    exact analyticAt_const.add ((LinearMap.toContinuousLinearMap (blk b)).analyticAt t)
  refine ⟨hFa.comp hA (Set.mapsTo_univ _ _), ?_⟩
  intro x hx t
  have hX : blk b x ∈ powLat ΛM N N' := by
    intro i j
    by_cases h : (i, j) = b
    · have e : (fun τ => blk b x τ i j) = x := funext fun τ => by simp [blk_apply, h]
      rw [e]
      exact hx
    · have e : (fun τ => blk b x τ i j) = 0 := funext fun τ => by simp [blk_apply, h]
      rw [e]
      exact ΛM.zero_mem
  have key := hFf (blk b x) hX (upd z b t)
  simp only [opU] at key ⊢
  have e2 : formV (Formalism.L2.Th1.F.area L) n N N' (upd z b t) (blk b x) = matH (hOne L n) t x := by
    rw [formV_blk, matH_hOne]
    simp [upd]
  have e3 : formV (Formalism.L2.Th1.F.area L) n N N' (blk b x) (blk b x) = matH (hOne L n) x x := by
    rw [formV_blk, matH_hOne]
    simp [blk_apply]
  have e4 : alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') (blk b x) =
      alphaQ c (matH (hOne L n)) x := by
    simp only [alphaQ, qOf, e3]
  rw [upd_add, e2, e3, e4] at key
  exact key

end PI.KerTens.W
