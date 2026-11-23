import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSidePos

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model

def SharpFormAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)), B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m d vec)),
        (∀ P ∈ nabO O Kf m (nuOf (letterWt m d vec)), B P Q ∈ Set.range (algebraMap O Kf)) →
          Q ∈ nabO O Kf m (nuOf (letterWt m d vec))) ∧
      (∀ Q ∈ nabO O Kf m (nuOf (letterWt m d vec)), ∀ P ∈ nabO O Kf m (nuOf (letterWt m d vec)),
        B P (((p : Kf) ^ (m * Nat.log p d)) • Q) ∈ Set.range (algebraMap O Kf))

end Formalism.MainNotions.ColumnSystems.Pf
