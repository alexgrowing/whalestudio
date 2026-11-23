import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.ProductThetaMem

noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.KerTens

open Formalism.L2.Th1.H (Sesq matH alphaQ)

def hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] : Matrix n n ℂ :=
  ((Formalism.L2.Th1.F.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ)

def tensPow {n : Type} (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def powLat {n : Type} (ΛM : AddSubgroup (n → ℂ)) (N N' : ℕ) : AddSubgroup (n → Fin N' → Fin N → ℂ) where
  carrier := {z | ∀ i j, (fun τ => z τ i j) ∈ ΛM}
  zero_mem' := fun _ _ => ΛM.zero_mem
  add_mem' := fun hx hy i j => ΛM.add_mem (hx i j) (hy i j)
  neg_mem' := fun hx i j => ΛM.neg_mem (hx i j)

def formV (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : Sesq (n → Fin N' → Fin N → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun z w => (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)
    (by intro a b c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, ← mul_div_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def TensSpans : Prop :=
  ∀ (c : ℝ) (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (ΛM : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ),
    (∀ F ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ) →
    ∀ (N N' : ℕ), ∀ F ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N')
      (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N')) (powLat ΛM N N'), ∃ a : ℂ, F = a • tensPow θ N N'

end PI.KerTens
