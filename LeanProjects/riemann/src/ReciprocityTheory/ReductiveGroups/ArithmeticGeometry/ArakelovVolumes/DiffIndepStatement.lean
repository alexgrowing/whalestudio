import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.AR

def DiffIndepStatement.{u, v} : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] (D : ℕ)
    (x : Fin D → Ω),
    LinearIndependent Ω (fun k => KaehlerDifferential.D K Ω (x k)) → AlgebraicIndependent K x

def DiffBasisStatement.{u, v} : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω] [CharZero K] (D : ℕ)
    (x : Fin D → Ω),
    (⊤ : IntermediateField K Ω).FG → Algebra.trdeg K Ω = D →
    LinearIndependent Ω (fun k => KaehlerDifferential.D K Ω (x k)) →
    FiniteDimensional (IntermediateField.adjoin K (Set.range x)) Ω ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (Set.range x)) Ω

end ReciprocityTheory.ChartRestriction.G.AR
