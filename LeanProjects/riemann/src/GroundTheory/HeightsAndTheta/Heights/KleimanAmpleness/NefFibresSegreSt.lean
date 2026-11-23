import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefGenericDVRSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def NefFibresSegre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (NumbersDVR.MRing ι O)) (d : ℕ)
    (β : K → ℤ), NumbersDVR.IsModelOver P d →
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra O Ω) (_ : Algebra (FractionRing O) Ω)
      (_ : IsScalarTower O (FractionRing O) Ω) (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle O x),
      (Kleiman.NefAbove M.toSubSystem ((IsLocalRing.maximalIdeal O).map (C : O →+* Kleiman.Poly O N)) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O) (NumbersDVR.specialIdeal P) β) ∧
      (Kleiman.Nef (M.toSubSystem.extend (FractionRing O)) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib P) β)

theorem NefFibresSegre.hyps :
    NumbersDVR.IsModelOver (⊥ : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin 2) exO)) 1 :=
  NumbersDVR.isModelOver_projectiveSpace 1

example (h : NefFibresSegre.Statement) :=
  h exO Unit (fun _ => Fin 2) ⊥ 1 (fun _ => 1) NefFibresSegre.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
