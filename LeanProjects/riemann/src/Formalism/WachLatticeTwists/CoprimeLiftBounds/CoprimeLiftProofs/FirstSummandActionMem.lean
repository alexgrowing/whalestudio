import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

section T1
variable {A T' G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Group G]

lemma first_summand_action_mem (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) (g : G) (b : FirstSummandSubmodule O e₁) :
    ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)) ∈ FirstSummandSubmodule O e₁ := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp b.2
  rw [LinearMap.mulLeft_apply] at hx
  show _ ∈ LinearMap.range (LinearMap.mulLeft O e₁)
  rw [LinearMap.mem_range]
  refine ⟨((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (x * r g⁻¹)), ?_⟩
  rw [LinearMap.mulLeft_apply, mul_smul_comm, mul_smul_comm, ← mul_assoc, hx]

def firstSummandRep (O : Type*) [CommRing O] [Algebra O A] (r : G →* A) (χ : G →* T'ˣ) (e₁ : A)
    (ε : G →* Oˣ) : Representation O G (FirstSummandSubmodule O e₁) where
  toFun g :=
    { toFun := fun b => ⟨_, first_summand_action_mem O r χ e₁ ε g b⟩
      map_add' := fun b b' => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (((b : A) + (b' : A)) * r g⁻¹)) = _ + _
        rw [add_mul, smul_add, smul_add])
      map_smul' := fun c b => Subtype.ext (by
        show ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((c • (b : A)) * r g⁻¹)) =
          c • (((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)))
        rw [smul_mul_assoc, smul_comm _ c, smul_comm _ c]) }
  map_one' := LinearMap.ext fun b => Subtype.ext (by
    show ((ε 1 : Oˣ) : O) • (((χ 1 : T'ˣ) : T') • ((b : A) * r 1⁻¹)) = (b : A)
    simp)
  map_mul' g h := LinearMap.ext fun b => Subtype.ext (by
    show ((ε (g * h) : Oˣ) : O) • (((χ (g * h) : T'ˣ) : T') • ((b : A) * r (g * h)⁻¹)) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') •
        ((((ε h : Oˣ) : O) • (((χ h : T'ˣ) : T') • ((b : A) * r h⁻¹))) * r g⁻¹))
    rw [map_mul, map_mul, mul_inv_rev, map_mul, Units.val_mul, Units.val_mul, smul_mul_assoc,
      smul_mul_assoc, mul_smul, mul_smul, mul_assoc,
      smul_comm ((χ g : T'ˣ) : T') ((ε h : Oˣ) : O)])

end T1

theorem t1 : FirstSummandRepresentation := by
  intro O A T' G _ _ _ _ _ _ r χ e₁ ε
  exact ⟨firstSummandRep O r χ e₁ ε, fun g b => rfl⟩

end Formalism.RepresentationBoundsCohomology.BR
