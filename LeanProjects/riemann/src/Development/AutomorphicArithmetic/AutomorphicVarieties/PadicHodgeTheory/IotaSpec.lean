import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes

noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {Ω : Type} [Field Ω] [CharZero Ω] {v : ℕ} [Fact v.Prime]

def placeJ (j : Ω →+* Om v) : ValuationSubring Ω := (Valued.v : Valuation (Om v) NNReal).valuationSubring.comap j

variable [IsAlgClosure ℚ Ω]

def iota (j : Ω →+* Om v) : GQ v →* G ℚ Ω :=
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Om v) Ω).comp
    { toFun := fun σ => σ.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem iota_spec (j : Ω →+* Om v) (σ : GQ v) (y : Ω) : j (iota j σ y) = σ (j y) := by
  letI : Algebra Ω (Om v) := j.toAlgebra
  haveI : IsScalarTower ℚ Ω (Om v) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) Ω y

theorem exists_emb : Nonempty (Ω →+* Om v) := ⟨(IsAlgClosed.lift (R := ℚ) (S := Ω) (M := Om v)).toRingHom⟩

end UpperTheory.V.Loc
