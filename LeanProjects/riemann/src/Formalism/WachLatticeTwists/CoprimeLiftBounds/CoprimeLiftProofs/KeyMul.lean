import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.LengthMapQuotLe
import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

lemma key_mul {O A T' G : Type*} [CommRing O] [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
    [Group G] (r : G →* A) (χ : G →* T'ˣ) (g : G) (c : O) (b x : A) :
    (c • (((χ g : T'ˣ) : T') • (b * r g⁻¹))) * (uElt r χ g * x) = c • (b * x) := by
  have hr : r g⁻¹ * r g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [uElt, smul_mul_assoc, mul_smul_comm, smul_smul, Units.mul_inv, one_smul]
  rw [mul_assoc, ← mul_assoc (r g⁻¹), hr, one_mul]
  rw [smul_comm (((χ g)⁻¹ : T'ˣ) : T') c, smul_smul, Units.inv_mul, one_smul]

theorem rowCup : StatRowCup := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ _ r χ E e₁ δ ι _ D j Kc k0 Dw ε T₁ T₂ _ _ _ _ ρ₁ ρ₂
    inc π γ lam C₁ CN2 CN CA CP hinc hπ hγ hc2 hc1 hCP hH2 φ a ha hCa
  let Y := Ymod r χ E
  let ρY : Representation O Dw Y := resRep (uRep O (M := Y) r χ) Dw
  let ρA : Representation O Dw A := resRep (uRep O (M := A) r χ) Dw
  let ρM : Representation O Dw M := resRep (uRep O (M := M) r χ) Dw
  let β : T₁ →ₗ[O] Y →ₗ[O] Y := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add, add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let β' : T₁ →ₗ[O] A →ₗ[O] A := LinearMap.mk₂ O (fun b y => inc b • y)
    (fun b b' y => by rw [map_add, add_smul]) (fun c b y => by rw [map_smul, smul_assoc])
    (fun b y y' => smul_add _ _ _) (fun c b y => smul_comm _ _ _)
  let jm : Y →ₗ[O] A := Y.subtype.restrictScalars O
  let φ' : Y →ₗ[O] M := psiY r χ E e₁ δ D j Kc k0 φ
  have hφ' : ∀ (x : A) (y : Y), φ' (x • y) = x • φ' y := fun x y => map_smul
      (φ ∘ₗ (Submodule.mkQ _) ∘ₗ (LinearMap.inl A (Ymod r χ E) _)) x y
  exact cupKillAdm O Dw T₁ Y A Y A T₂ M (KO O) ρ₁ ρY ρA (twRep ε Y) (twRep ε A) ρ₂ ρM
    (twRep ε (KO O)) β β' γ jm jm π φ' (lam ∘ₗ φ') CN2 CN CA CP
    (fun g b y => Subtype.ext (by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * (y : A)) = ((ε g : Oˣ) : O) • (inc b * (y : A))
      rw [hinc, key_mul]))
    (fun g b y => by
      show inc (ρ₁ g b) * (uElt r χ (g : G) * y) = ((ε g : Oˣ) : O) • (inc b * y)
      rw [hinc, key_mul])
    (fun g y => rfl) (fun g y => rfl) hπ (fun g y => hφ' _ y)
    (fun g y => by
      show (lam ∘ₗ φ') (((ε g : Oˣ) : O) • y) = ((ε g : Oˣ) : O) • (lam ∘ₗ φ') y
      rw [map_smul])
    (fun m n => rfl)
    (fun m n => by
      show γ (π m) (φ' n) = lam (φ' (inc m • n))
      rw [hγ, hφ'])
    (fun f hf => hCP _ f hf) hH2 a (fun h => yY r χ E (h : G)) E ha
    (fun g h => Subtype.ext (ycoc_mul r χ E (g : G) (h : G)))
    (fun g => by
      show ycoc r χ E (g : G) = uElt r χ (g : G) * E - E
      unfold ycoc uElt
      rw [sub_mul, one_mul])
    (hc2 a hCa) (hc1 a hCa)

end Formalism.RepresentationBoundsCohomology.BR
