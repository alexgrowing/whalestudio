import Mathlib
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolReal
import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolBridge
import GroundTheory.ProfiniteCohomology.CartierDual
import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

attribute [local instance 2000] Rep.hV2

section TateZero

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

def normClasses (A : Rep k G) [IsDiscreteRep A] : Submodule k (cohomology A 0) :=
  (normRangeInvariants A).map (H0Iso A).inv.hom

theorem mem_normClasses_iff (A : Rep k G) [IsDiscreteRep A] (x : cohomology A 0) :
    x ∈ normClasses A ↔ ∃ a : A, ∃ h : A.ρ.norm a ∈ A.ρ.invariants,
      x = (H0Iso A).inv.hom ⟨A.ρ.norm a, h⟩ := by
  constructor
  · rintro ⟨y, ⟨a, ha⟩, rfl⟩
    refine ⟨a, ha ▸ y.2, ?_⟩
    congr 1
    exact Subtype.ext ha.symm
  · rintro ⟨a, h, rfl⟩
    exact ⟨⟨A.ρ.norm a, h⟩, ⟨a, rfl⟩, rfl⟩

abbrev cohomologyTateZero (A : Rep k G) [IsDiscreteRep A] : Type :=
  cohomology A 0 ⧸ normClasses A

end TateZero

section Pairing

variable (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω]
  (h2 : Module.finrank F Ω ≤ 2)
  (hN : ∀ a b : Fˣ, (a : F) ∉ Set.range (Algebra.norm F : Ω → F) →
    (b : F) ∉ Set.range (Algebra.norm F : Ω → F) →
      ((a * b : Fˣ) : F) ∈ Set.range (Algebra.norm F : Ω → F))

def realInv : cohomology (galUnits.{0} F Ω) 2 →+ QZ :=
  (quadraticInv F Ω h2 hN).comp (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2).toAddMonoidHom

theorem realInv_apply (x : cohomology (galUnits.{0} F Ω) 2) :
    realInv F Ω h2 hN x = quadraticInv F Ω h2 hN (cohomologyULiftIntAddEquiv (galUnits.{0} F Ω) 2 x) :=
  rfl

def realDualityPairing (M : Rep (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M] {r s : ℕ}
    (h : r + s = 2) : cohomology M r →+ cohomology (cartierDual F Ω M) s →+ QZ :=
  (AddMonoidHom.compHom (realInv F Ω h2 hN)).comp
    (bilinAddHom (cupPairing (cartierPairing F Ω M) h))

theorem realDualityPairing_apply (M : Rep (ULift.{0} ℤ) Gal(Ω/F)) [IsDiscreteRep M] [Finite M]
    {r s : ℕ} (h : r + s = 2) (x : cohomology M r) (y : cohomology (cartierDual F Ω M) s) :
    realDualityPairing F Ω h2 hN M h x y =
      realInv F Ω h2 hN (cupPairing (cartierPairing F Ω M) h x y) :=
  rfl

end Pairing

end GroundTheory.ProfCoh
