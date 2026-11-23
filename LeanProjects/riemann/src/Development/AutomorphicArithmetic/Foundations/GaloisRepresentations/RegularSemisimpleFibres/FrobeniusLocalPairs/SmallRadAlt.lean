import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.ElemPairJ

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

def BallLev : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ K : Subgroup (GL (Fin n) k), (K : Set (GL (Fin n) k)) = ball n r → IwLev K ∧ ∀ t, dcos K t = elemSet r {t}

def LevOf : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (r : ValueGroupWithZero k),
    0 < r → r < 1 → ∀ D : Subgroup (Fin n → kˣ), IsCompact (D : Set (Fin n → kˣ)) → (∀ d ∈ D, ∀ i, valuation k (d i : k) = 1) →
    ∃ K : Subgroup (GL (Fin n) k), (∀ g, g ∈ K ↔ ∃ a ∈ ball n r, ∃ d ∈ D, g = a * diagT k (Fin n) d) ∧ IwLev K ∧
      ∀ t, dcos K t = elemSet r {x | ∃ d ∈ D, x = t * d}

def SmallRad : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (∀ U : Set (GL (Fin n) k), U ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ball n r' ⊆ U) ∧
    (∀ W : Set (Fin n → kˣ), W ∈ nhds 1 → ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ r' ≤ r, ∀ u, Near r' u → u ∈ W) ∧
    (∀ r : ValueGroupWithZero k, r < 1 → ∃ D : Subgroup (Fin n → kˣ), (∀ u, u ∈ D ↔ Near r u) ∧ IsCompact (D : Set (Fin n → kˣ))) ∧
    Continuous (diagT k (Fin n)) ∧ (∃ t : Fin n → kˣ, Strict t) ∧ ∀ t₀ t : Fin n → kˣ, Strict t₀ → Dom t → Strict (t₀ * t)

end UpperTheory.Gal.InertialTypesAlt.L
