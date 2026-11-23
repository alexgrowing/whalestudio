import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementA
import Formalism.PolynomialDimension.MultinomialDepth.MonoCount

namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity

section gen

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

def res (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) : GlW K U n where
  E := fun a b => (G.E a b).restrict (fun x hx => hU a b x hx)
  comm := fun a b c d x => by
    apply Subtype.ext
    have := G.comm a b c d (x : V)
    split_ifs at this ⊢ <;> simpa using this
  comp := fun μ => (G.comp μ).restrict (fun x hx => G.graded_of hU μ x hx)
  dec := fun x => by
    obtain ⟨S, hS⟩ := G.dec (x : V)
    exact ⟨S, fun μ hμ => Subtype.ext (by simpa using hS μ hμ)⟩
  sum_comp := fun x S hS => by
    apply Subtype.ext
    have := G.sum_comp (x : V) S (fun μ hμ => by simpa using congrArg Subtype.val (hS μ hμ))
    simpa using this
  idem := fun μ ν x => by
    apply Subtype.ext
    have := G.idem μ ν (x : V)
    split_ifs at this ⊢ <;> simpa using this
  diag := fun c μ x => by
    apply Subtype.ext
    simpa using G.diag c μ (x : V)
  shift := fun a b μ x => by
    apply Subtype.ext
    simpa using G.shift a b μ (x : V)

def IsoW (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : Submodule K V :=
  G.gS {v | G.IsHW la v ∧ v ∈ W}

def WtBound2 {V₁ V₂ : Type} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ) : Prop :=
  ∀ (μ ν : Fin n → ℤ) (x : V₁) (y : V₂), x ≠ 0 → y ≠ 0 → y ∈ W → G₁.IsWt μ x → G₂.IsWt ν y → ∀ c, |ν c - μ c| ≤ (l : ℤ)

end gen

section padic

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}

def DeltaLat (G : GlW ℚ_[p] V n) (s : Set V) : AddSubgroup V :=
  sInf {L | s ⊆ L ∧ ZpClosed p L ∧ DivStable G.E L}

def HasLatBasis (M : AddSubgroup V) (U : Submodule ℚ_[p] V) : Prop :=
  ∃ (k : ℕ) (b : Module.Basis (Fin k) ℚ_[p] U), (∀ i, ((b i : U) : V) ∈ M) ∧
    ∀ x : U, (x : V) ∈ M → ∀ i, ‖b.repr x i‖ ≤ 1

structure LatData (G : GlW ℚ_[p] V n) (W : Submodule ℚ_[p] V) (M : AddSubgroup V) (l : ℕ) : Prop where
  stable : G.Stable W
  fd : FiniteDimensional ℚ_[p] W
  finW : G.FinW W
  bound : ∀ (μ ν : Fin n → ℤ) (x y : V), x ≠ 0 → y ≠ 0 → x ∈ W → y ∈ W → G.IsWt μ x → G.IsWt ν y →
    ∀ c, |ν c - μ c| ≤ (l : ℤ)
  closed : ZpClosed p M
  div : DivStable G.E M
  graded : ∀ μ, ∀ x ∈ M, G.comp μ x ∈ M
  basis : ∀ U : Submodule ℚ_[p] V, U ≤ W → HasLatBasis p M U

end padic

end Formalism.InvariantFactorPaths.PW
