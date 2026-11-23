import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def m0Z (lam : Fin n → ℤ) : Fin n → ℤ := fun a => 2 * lam a + ((n : ℤ) - 1) - 2 * ((a : ℕ) : ℤ)

def wtR (μ : Fin n → ℤ) : Fin n → ℝ := fun a => (μ a : ℝ)

def DomLE (ν m : Fin n → ℝ) : Prop :=
  (∀ k : ℕ, ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), ν a ≤ ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), m a) ∧
    ∑ a, ν a = ∑ a, m a

def wtDual (E : KMod n) (μ : Fin n → ℤ) : Submodule ℂ (E.V →L[ℂ] ℂ) where
  carrier := {ξ | ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z →
    ξ ∘L E.ρ k⁻¹ = (∏ a, z a ^ μ a) • ξ}
  add_mem' {x y} hx hy k z hk := by
    rw [ContinuousLinearMap.add_comp, hx k z hk, hy k z hk, smul_add]
  zero_mem' k z _ := by simp
  smul_mem' c x hx k z hk := by
    rw [ContinuousLinearMap.smul_comp, hx k z hk, smul_comm]

def IsCliff {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ a b d e, c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : Matrix ι ι ℂ) else 0) ∧
    ∀ a b, (c a b)ᴴ = c b a

def spinM {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b - if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0

def yF {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    Module.End ℂ (ι → V) where
  toFun x := fun i => Kf a b (x i) + ∑ j, spinM c a b i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
    abel
  map_smul' s x := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.CompanionTheory.RealCount
