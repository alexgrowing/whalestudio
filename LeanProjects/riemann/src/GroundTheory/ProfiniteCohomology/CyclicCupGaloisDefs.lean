import Mathlib
import GroundTheory.ProfiniteCohomology.CyclicCupDefs
import GroundTheory.ProfiniteCohomology.Characters
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
import GroundTheory.ProfiniteCohomology.GaloisModules.Discrete
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Generic

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

noncomputable def cupRightProf (h : p + q = n) (b : cohomology B q) :
    cohomology A p ⟶ cohomology (A ⊗ B) n :=
  ModuleCat.ofHom ((cup h).flip b)

theorem cupRightProf_apply (h : p + q = n) (b : cohomology B q) (a : cohomology A p) :
    (cupRightProf h b).hom a = cup h a b :=
  rfl

end Generic

section Profinite

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

noncomputable def charClassProf (χ : Additive G →ₜ+ QZ) : cohomology (Rep.trivial ℤ G ℤ) 2 :=
  (δ (GroundTheory.GroupCoh.ratSES_shortExact G) 1 2 rfl).hom ((cohomologyOneRatModIntIso G).inv.hom χ)

noncomputable def cupCharClassProf (A : Rep ℤ G) [IsDiscreteRep A] (χ : Additive G →ₜ+ QZ) :=
  (H0Iso A).inv ≫ cupRightProf (A := A) (B := Rep.trivial ℤ G ℤ) (zero_add 2) (charClassProf χ) ≫
    cohomologyMap (A := A ⊗ Rep.trivial ℤ G ℤ) (B := A) (ρ_ A).hom 2

end Profinite

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L]

def unitsInvariant (a : Kˣ) : (galUnitsZ K L).ρ.invariants :=
  ⟨Additive.ofMul (Units.map (algebraMap K L : K →* L) a), fun σ => by
    apply Additive.toMul.injective
    apply Units.ext
    change ((galUnitsHom K L σ (Units.map (algebraMap K L : K →* L) a) : Lˣ) : L) =
      (Units.map (algebraMap K L : K →* L) a : L)
    rw [coe_galUnitsHom_apply]
    simp⟩

@[simp]
theorem coe_unitsInvariant (a : Kˣ) :
    ((Additive.toMul (unitsInvariant K L a : Additive Lˣ) : Lˣ) : L) = algebraMap K L a :=
  rfl

variable [IsGalois K L]

noncomputable def galCupClass (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    cohomology (galUnitsZ K L) 2 :=
  (cupCharClassProf (galUnitsZ K L) χ).hom (unitsInvariant K L a)

end Galois

end GroundTheory.ProfCoh
