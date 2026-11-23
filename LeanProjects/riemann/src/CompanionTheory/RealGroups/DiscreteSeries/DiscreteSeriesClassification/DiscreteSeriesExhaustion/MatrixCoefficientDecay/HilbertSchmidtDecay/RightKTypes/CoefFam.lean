import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.RigidityTheorems.IsInLieAlgebraISmulAddConjTranspose

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev CoefFam (X : GMod n) (I : Type) : Type := I → (X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ))

def LeftExp (ε : Fin n → Bool) {X : GMod n} {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i, ∃ (r : ℕ) (is : Fin r → I) (β : Fin r → S7.KG ε → ℂ) (B : ℝ), (∀ l k, ‖β l k‖ ≤ B) ∧
    ∀ (v : X.V) (g : S7.UJ ε) (k : S7.KG ε), c i v (S7.toMK k * S7.toM g) = ∑ l, β l k * c (is l) v (S7.toM g)

def ContFam (ε : Fin n → Bool) {X : GMod n} {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i v, Continuous fun g : S7.UJ ε => c i v (S7.toM g)

structure KAct (ε : Fin n → Bool) (X : GMod n) : Type 1 where
  N : Type
  [ng : NormedAddCommGroup N]
  [ns : NormedSpace ℂ N]
  emb : X.V →ₗ[ℂ] N
  inj : Function.Injective emb
  ρ : S7.KG ε → Module.End ℂ X.V
  compat : ∀ k a b x, ρ k (X.E a b x) = ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • X.E c d (ρ k x)
  bdd : ∃ C : ℝ, ∀ k x, ‖emb (ρ k x)‖ ≤ C * ‖emb x‖
  fin : ∀ x, ∃ W : Submodule ℂ X.V, FiniteDimensional ℂ W ∧ ∀ k, ρ k x ∈ W

attribute [instance] KAct.ng KAct.ns

def RightEq {ε : Fin n → Bool} {X : GMod n} (A : KAct ε X) {I : Type} (c : CoefFam X I) : Prop :=
  ∀ i v (g : S7.UJ ε) (k : S7.KG ε), c i v (S7.toM g * S7.toMK k) = c i (A.ρ k v) (S7.toM g)

end CompanionTheory.RgExh.Dec.L.WyKR
