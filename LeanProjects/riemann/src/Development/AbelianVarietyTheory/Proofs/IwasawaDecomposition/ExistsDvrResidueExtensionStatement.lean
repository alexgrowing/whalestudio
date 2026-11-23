import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrResidueExtension
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open IsLocalRing GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_residue_extension : ∀ {A : Type} [CommRing A] [IsLocalRing A] {L : Type} [Field L] (φ : ResidueField A →+* L), φ.Finite → CharZero (ResidueField A) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (α : A →+* W), IsLocalHom α → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (f : W →+* V), CDvr V ∧ Function.Injective f ∧ IsLocalHom f ∧ ∃ σ : L →+* ResidueField V, ∀ a : A, σ (φ (residue A a)) = residue V (f (α a)) := by
  first | exact @GlobalTheory.exists_cDvr_residue_lift | exact GlobalTheory.exists_cDvr_residue_lift | (intros; apply GlobalTheory.exists_cDvr_residue_lift <;> assumption)
