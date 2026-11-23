import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFielStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerTail

theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.triangle_succ, Nat.triangle_succ, ih]
    ring

variable {g : ℕ} [Fact g.Prime]

theorem entN_tl (m : ℕ) {n : ℕ} (M : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) :
    entN (tl m M) a b = entN M a b := by
  rw [entN, dif_pos ⟨ha, hb⟩]; rfl

theorem entN_fin {n : ℕ} (M : Mt g n) (a b : Fin n) : entN M a b = M a b := by
  rw [entN, dif_pos ⟨a.2, b.2⟩]

theorem inR_iff (i : ℕ) {n : ℕ} (M : Mt g n) :
    InR i M ↔ ∀ a : ℕ, i ≤ a → a < n → (∀ b, b < a → entN M a b = 0) ∧ entN M a a = 1 := by
  constructor
  · rintro ⟨h1, h2⟩ a hia han
    refine ⟨fun b hb => ?_, ?_⟩
    · by_cases hbi : b < i
      · have := h1 ⟨a, han⟩ ⟨b, by omega⟩ hbi hia
        exact (entN_fin M ⟨a, han⟩ ⟨b, by omega⟩).trans this
      · have := (h2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩).1 (by simp only [Fin.mk_lt_mk]; omega)
        simp only [br] at this
        rwa [show i + (a - i) = a by omega, show i + (b - i) = b by omega] at this
    · have := (h2 ⟨a - i, by omega⟩ ⟨a - i, by omega⟩).2 rfl
      simp only [br] at this
      rwa [show i + (a - i) = a by omega] at this
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ⟨fun hab => ?_, fun hab => ?_⟩⟩
    · exact (entN_fin M a b).symm.trans ((h a ha a.2).1 b (by omega))
    · have := a.2
      have hab' : (b : ℕ) < a := hab
      exact (h (i + a) (by omega) (by omega)).1 (i + b) (by omega)
    · subst hab
      have := a.2
      exact (h (i + a) (by omega) (by omega)).2

theorem inR_split {i m n : ℕ} (him : i ≤ m) (hmn : m ≤ n) (M : Mt g n) :
    InR i M ↔ InR m M ∧ InR i (tl m M) := by
  simp only [inR_iff]
  constructor
  · intro h
    refine ⟨fun a ha han => h a (by omega) han, fun a ha ham => ⟨fun b hb => ?_, ?_⟩⟩
    · rw [entN_tl m M ham (by omega)]
      exact (h a ha (by omega)).1 b hb
    · rw [entN_tl m M ham ham]
      exact (h a ha (by omega)).2
  · rintro ⟨h1, h2⟩ a ha han
    by_cases ham : a < m
    · refine ⟨fun b hb => ?_, ?_⟩
      · rw [← entN_tl m M ham (by omega)]
        exact (h2 a ha ham).1 b hb
      · rw [← entN_tl m M ham ham]
        exact (h2 a ha ham).2
    · exact h1 a (by omega) han

theorem tl_tl {i m n : ℕ} (him : i ≤ m) (M : Mt g n) : tl i (tl m M) = tl i M := by
  funext a b
  have := a.2
  have := b.2
  exact entN_tl m M (by omega) (by omega)

theorem supFrom_split {i m n : ℕ} (him : i < m) (hmn : m ≤ n) (M : Mt g n) :
    supFrom i M = supFrom (m - 1) M + supFrom i (tl m M) := by
  unfold supFrom
  rw [add_comm, ← Finset.sum_Ico_consecutive _ (show i ≤ m - 1 by omega) (show m - 1 ≤ n - 1 by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  exact (entN_tl m M (by omega) (by omega)).symm

theorem der_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ),
    i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  intro g _ ψ i m n F him hmn
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i m _ h him.le, GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h (by omega)]
  have he : i * (n - i) + (n - i) * (n - i - 1) / 2 =
      (i * (m - i) + (m - i) * (m - i - 1) / 2) + (m * (n - m) + (n - m) * (n - m - 1) / 2) := by
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le him.le
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [show i + a + b - i = a + b by omega, show i + a - i = a by omega, show i + a + b - (i + a) = b by omega,
      tri_add]
    ring
  rw [he, pow_add _ _ (m * (n - m) + (n - m) * (n - m - 1) / 2), mul_inv _ ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2)),
    mul_assoc]
  congr 1
  unfold tail
  set c : ℂ := ((g : ℂ) ^ (m * (n - m) + (n - m) * (n - m - 1) / 2))⁻¹
  have h1 : ∀ p : Gn g m, (if InR i (p : Mt g m) ∧ tl i (p : Mt g m) = (h : Mt g i) then
      (c * ∑ x : Gn g n, if InR m (x : Mt g n) ∧ tl m (x : Mt g n) = (p : Mt g m) then
        F x * (ψ (supFrom (m - 1) (x : Mt g n)))⁻¹ else 0) * (ψ (supFrom i (p : Mt g m)))⁻¹ else 0) =
      c * ∑ x : Gn g n, if tl m (x : Mt g n) = (p : Mt g m) then
        (if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
          F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0) else 0 := by
    intro p
    split_ifs with hp
    · rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx]
        rw [← hx] at hp
        rw [tl_tl him.le] at hp
        rw [inR_split him.le hmn (x : Mt g n), supFrom_split him hmn (x : Mt g n), AddChar.map_add_eq_mul, mul_inv,
          ← hx]
        by_cases hR : InR m (x : Mt g n)
        · rw [if_pos ⟨hR, rfl⟩, if_pos ⟨⟨hR, hp.1⟩, hp.2⟩, mul_assoc]
        · rw [if_neg (fun hh => hR hh.1), if_neg (fun hh => hR hh.1.1), zero_mul]
      · rw [if_neg hx, if_neg (fun hh => hx hh.2), zero_mul]
    · symm
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : tl m (x : Mt g n) = (p : Mt g m)
      · rw [if_pos hx, if_neg]
        rintro ⟨ha, hb⟩
        apply hp
        rw [← hx, tl_tl him.le]
        exact ⟨((inR_split him.le hmn _).1 ha).2, hb⟩
      · rw [if_neg hx]
  rw [Finset.sum_congr rfl fun p _ => h1 p, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i)
  · have hu : IsUnit (tl m (x : Mt g n)) :=
      ((GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g m (n - m) n (by omega)).2.2.1 x ((inR_split him.le hmn _).1 hx.1).1.1).1
    obtain ⟨p, hp⟩ := hu
    rw [Finset.sum_eq_single p]
    · rw [if_pos hp.symm]
    · intro q _ hq
      rw [if_neg]
      intro hh
      exact hq (Units.ext (hp.trans hh).symm)
    · intro hh
      exact absurd (Finset.mem_univ p) hh
  · simp [hx]

end GlobalTheory.GLm.DerTail
