import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.StatementMass

noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

def MIClass : Prop :=
  ∀ (R : Ranks) (H : Host R) (k : ℕ),
    letI := H.cmStar
    (∃ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm H.E k) (stdLat H.E k) s) ∧
    (∀ s, Formalism.ThetaLiftIndependence.IsClassReps (stdForm H.E k) (stdLat H.E k) s →
      massH H k = ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm H.E k) M) : ℕ) : ℝ)⁻¹) ∧
    (∀ M ∈ Formalism.HermitianLatticesTheory.genus (stdForm H.E k) (stdLat H.E k),
      0 < Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm H.E k) M)) ∧
    0 < massH H k

def DegOnePrime : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ), g.Prime →
    (placesOver E g).ncard = Module.finrank ℚ E →
    ∃ v : Ideal (𝓞 E), v.IsMaximal ∧ Nonempty ((𝓞 E ⧸ v) ≃+* ZMod g)

def RedHomGen : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (k g : ℕ), g.Prime →
    ∀ (v : Ideal (𝓞 E)), v.IsMaximal → Nonempty ((𝓞 E ⧸ v) ≃+* ZMod g) →
    ∀ (M : Submodule (𝓞 E) (Fin k → E)), Submodule.IsLattice E M →
    ∀ (G : Subgroup ((Fin k → E) ≃ₗ[E] (Fin k → E))),
      (∀ a ∈ G, ∀ x ∈ M, a x ∈ M) → (∀ a ∈ G, ∀ x ∈ M, a.symm x ∈ M) →
      ∃ ρ : G →* GL (Fin k) (ZMod g), ∀ a : G, IsOfFinOrder a →
        (∃ N : ℕ, ρ a ^ (g ^ N) = 1) → ∃ N : ℕ, a ^ (g ^ N) = 1

def IdxFacts : Prop :=
  (∀ (g k : ℕ), g.Prime → ∃ U : Subgroup (GL (Fin k) (ZMod g)),
    (∀ x, x ∈ U ↔ IsUnitri (x : Matrix (Fin k) (Fin k) (ZMod g))) ∧
    (U.index : ℝ) = idxColLoc g k ∧ 0 < U.index ∧
    ∀ x ∈ U, ∃ N : ℕ, x ^ (g ^ N) = 1) ∧
  (∀ (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X],
    (∀ (x : X) (a : G), a • x = x → a = 1) → Nat.card G ∣ Nat.card X)

end Formalism.MainNotions.Gaps.MI
