import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.IdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

open Formalism.MainNotions.TaylorLogMetric Formalism.BasicNotions

namespace Formalism.MainNotions.Ext

section Th

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

noncomputable def alG (s A : ℝ) (x : T → I → J → ℂ) : ℂ := (-1 : ℂ) ^ (round (s * (HfG A x x).re))

def ThSpG (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Set ((T → I → J → ℂ) → ℂ) :=
  {G | Differentiable ℂ G ∧ ∀ x ∈ La', ∀ z, alG s A x * UG A x G z = G z}

noncomputable def normSqG (A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) : ℝ :=
  let Fd : Set (T → I → J → ℂ) :=
    Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain La' Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (HfG A z z).re)

noncomputable def IopG (s A : ℝ) (La₁ La₂ : AddSubgroup (T → I → J → ℂ)) (G : (T → I → J → ℂ) → ℂ) :
    (T → I → J → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      alG s A ((Quotient.out q : La₂) : T → I → J → ℂ) * UG A ((Quotient.out q : La₂) : T → I → J → ℂ) G z

def GoodLat (s A : ℝ) (La' : AddSubgroup (T → I → J → ℂ)) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (T → I → J → ℂ)), La' = AddSubgroup.closure (Set.range b)) ∧
  (∀ x ∈ La', ∀ y ∈ La', ∃ n : ℤ, (HfG A x y).im = n) ∧
  (∀ v : T → I → J → ℂ, (∀ x ∈ La', ∃ n : ℤ, (HfG A v x).im = n) → v ∈ La') ∧
  ∀ x ∈ La', ∀ y ∈ La', ∀ n : ℤ, (HfG A x y).im = n → alG s A (x + y) = alG s A x * alG s A y * (-1 : ℂ) ^ n

end Th

def ThetaLineG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La' : AddSubgroup (T → I → J → ℂ), GoodLat s A La' →
      ∃ G ∈ ThSpG s A La', G ≠ 0 ∧ ∀ F ∈ ThSpG s A La', ∃ c : ℂ, F = fun z => c * G z

def IopUnitaryG : Prop :=
  ∀ (T I J : Type) [Fintype T] [Fintype I] [Fintype J] (s A : ℝ), 0 < A →
    ∀ La₁ La₂ : AddSubgroup (T → I → J → ℂ), GoodLat s A La₁ → GoodLat s A La₂ →
      (La₁.addSubgroupOf La₂).index ≠ 0 → (La₂.addSubgroupOf La₁).index ≠ 0 →
      ∀ th ∈ ThSpG s A La₁,
        IopG s A La₁ La₂ th ∈ ThSpG s A La₂ ∧
        normSqG A La₂ (IopG s A La₁ La₂ th) = normSqG A La₁ th ∧
        IopG s A La₂ La₁ (IopG s A La₁ La₂ th) = th

def GoodLa (D : D7) : Prop :=
  ∀ (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    0 < area (lamOf D cc δ) ∧
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (NumberField.RingOfIntegers D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      GoodLat (Real.sqrt D.host.d / 2) (area (lamOf D cc δ)) (La D (tor0 D cc δ) L₁ L₁') ∧
      ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) L₂ L₂')).index ≠ 0

end Formalism.MainNotions.Ext
