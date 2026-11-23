import Mathlib
import GroundTheory.ProfiniteCohomology.EulerCharDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u w

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] {R : Type w} [CommMonoid R]

structure IsMultiplicativeOn (P : ℕ → Prop) (χ : (A : Rep.{u} k G) → [IsDiscreteRep A] → R) :
    Prop where

  iso : ∀ {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [Finite A],
    P (Nat.card A) → (A ≅ B) → χ A = χ B

  shortExact : ∀ {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁] [IsDiscreteRep S.X₂]
    [IsDiscreteRep S.X₃] [Finite S.X₂], S.ShortExact → P (Nat.card S.X₂) →
    χ S.X₂ = χ S.X₁ * χ S.X₃

end GroundTheory.ProfCoh
