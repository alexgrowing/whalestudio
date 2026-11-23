import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PosCoreLetter
import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.TransposeWordsProofs.WeylFormNondegenerateGlobal

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.L2.G.Model Formalism.L2.G.Model.TS

def SharpDAt : Prop :=
  ∀ (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    [IsFractionRing O Kf] [CharZero Kf], p.Prime → ¬ IsUnit ((p : ℕ) : O) →
    ∀ (m d : ℕ) (vec : Bool), 1 ≤ m →
    ∀ Q ∈ Formalism.L2.G.Model.nabO O Kf m (nuOf (letterWt m d vec)), ∀ P ∈ Formalism.L2.G.Model.nabO O Kf m (nuOf (letterWt m d vec)),
      (fockR (hw Kf (le_refl (m + 1)) (nuOf (letterWt m d vec))) (hw Kf (le_refl (m + 1)) (nuOf (letterWt m d vec))))⁻¹ *
        fockR P (((p : Kf) ^ (m * Nat.log p d)) • Q) ∈ Set.range (algebraMap O Kf)

def SettingCharZeroAt : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (jO : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ jO w → CharZero Kf ∧ ¬ IsUnit ((p : ℕ) : O)

end Formalism.MainNotions.ColumnSystems.Pf
