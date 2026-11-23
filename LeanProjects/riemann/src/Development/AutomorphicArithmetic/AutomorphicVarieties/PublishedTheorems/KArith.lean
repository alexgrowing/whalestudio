import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.IsAcyclicSpace
import Formalism.GaloisCohomology.Statement

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.KL
open scoped TensorProduct

namespace UpperTheory.V.Published

def KFinGen : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (M : Plus (𝓞 L)) (k : ℕ), Group.FG (M.K (k + 1))

def KBorelRank : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (M : Plus (𝓞 L)) (k : ℕ),
    Module.finrank ℤ (Additive (M.K (k + 2))) =
      if (k + 2) % 4 = 1 then nrRealPlaces L + nrComplexPlaces L else if (k + 2) % 4 = 3 then nrComplexPlaces L else 0

def KFiniteField : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (M : Plus F) (i : ℕ),
    Subsingleton (M.K (2 * i + 2)) ∧ Nonempty (M.K (2 * i + 1) ≃* Multiplicative (ZMod (Nat.card F ^ (i + 1) - 1)))

def KLocalisation : Prop :=
  ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (a : R), a ≠ 0 →
    ∀ (M : Plus R) (M' : Plus (Localization.Away a))
      (Mv : ∀ v : {v : HeightOneSpectrum R // a ∈ v.asIdeal}, Plus (R ⧸ v.1.asIdeal)) (k : ℕ),
      ∃ (α : M.K (k + 2) →* M'.K (k + 2)) (δ : M'.K (k + 2) →* ∀ v, (Mv v).K (k + 1)), α.range = δ.ker

def KDwyerFriedlander : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (D : LData L Ω l), IsTotallyComplex L → (l = 2 → IsSquare (-1 : L)) →
    ∀ (M : Plus (𝓞 L)) (i : ℕ),
      ∃ p : ℤ_[l] ⊗[ℤ] Additive (M.K (2 * i + 2)) →ₗ[ℤ_[l]] H2 (zlTw D ((i : ℤ) + 2)), Function.Surjective p

end UpperTheory.V.Published

end
