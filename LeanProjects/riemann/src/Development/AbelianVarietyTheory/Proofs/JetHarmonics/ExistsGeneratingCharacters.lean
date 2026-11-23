import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsExtensionCharacter

namespace GlobalTheory.PrimaryCharacter

theorem exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  first
  | exact @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character
  | (apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExtensionCharacter.exists_extension_character <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExtensionCharacter.exists_extension_character ..)

theorem exists_factor_of_ker_le {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (χ : H →* Fˣ) (h : Φ.ker ≤ χ.ker) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by
  obtain ⟨κ, hκ⟩ := exists_extend_of_injective (QuotientGroup.kerLift Φ)
    (QuotientGroup.kerLift_injective Φ) (QuotientGroup.lift Φ.ker χ h)
  exact ⟨κ, fun x => hκ (QuotientGroup.mk x)⟩

end GlobalTheory.PrimaryCharacter
