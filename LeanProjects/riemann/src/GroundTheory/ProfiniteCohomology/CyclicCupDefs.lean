import Mathlib
import GroundTheory.TateCohomology.Characters
import GroundTheory.TateCohomology.CupProduct
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh

section Generic

universe u

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep k G} {p q n : ℕ}

noncomputable def cupRight (h : p + q = n) (b : groupCohomology B q) :
    groupCohomology A p ⟶ groupCohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cupH h).flip b)

end Generic

variable {G : Type} [Group G]

noncomputable def charClass (χ : Additive G →+ AddCircle (1 : ℚ)) : H2 (Rep.trivial ℤ G ℤ) :=
  groupCohomology.δ (ratSES_shortExact G) 1 2 rfl ((h1RatModIntIso G).inv χ)

noncomputable def cupCharClassH0 (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :
    H0 A ⟶ H2 A :=
  cupRight (A := A) (B := 𝟙_ (Rep ℤ G)) (zero_add 2) (charClass χ) ≫ map (MonoidHom.id G) (ρ_ A).hom 2

noncomputable def cupCharClass (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :=
  (H0Iso A).inv ≫ cupCharClassH0 A χ

end GroundTheory.ProfCoh
