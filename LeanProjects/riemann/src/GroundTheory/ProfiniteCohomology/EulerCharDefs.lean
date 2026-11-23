import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

variable (k G) in

def finiteDiscreteRep (P : ℕ → Prop) : ObjectProperty (Rep.{u} k G) :=
  fun A => IsDiscreteRep A ∧ Finite A ∧ P (Nat.card A)

variable (k G) in

def grothendieckRelations (P : ℕ → Prop) :
    AddSubgroup (FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory) :=
  AddSubgroup.closure {x | ∃ (S : ShortComplex (Rep.{u} k G)) (h₁ : finiteDiscreteRep k G P S.X₁)
    (h₂ : finiteDiscreteRep k G P S.X₂) (h₃ : finiteDiscreteRep k G P S.X₃), S.ShortExact ∧
      x = FreeAbelianGroup.of ⟨S.X₂, h₂⟩ - FreeAbelianGroup.of ⟨S.X₁, h₁⟩ -
        FreeAbelianGroup.of ⟨S.X₃, h₃⟩}

variable (k G) in

def GrothendieckGroup (P : ℕ → Prop) : Type (u + 1) :=
  FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory ⧸ grothendieckRelations k G P

instance (P : ℕ → Prop) : AddCommGroup (GrothendieckGroup k G P) :=
  inferInstanceAs (AddCommGroup (_ ⧸ grothendieckRelations k G P))

def GrothendieckGroup.mk {P : ℕ → Prop} (A : Rep.{u} k G) (hA : finiteDiscreteRep k G P A) :
    GrothendieckGroup k G P :=
  QuotientAddGroup.mk (s := grothendieckRelations k G P) (FreeAbelianGroup.of ⟨A, hA⟩)

variable [IsTopologicalGroup G]

variable (k G) in

def HasFiniteCohomology (P : ℕ → Prop) : Prop :=
  ∀ (A : Rep.{u} k G) [IsDiscreteRep A], Finite A → P (Nat.card A) →
    (∀ q : ℕ, Finite (cohomology A q)) ∧ ∀ q : ℕ, 3 ≤ q → Subsingleton (cohomology A q)

noncomputable def eulerChar (A : Rep.{u} k G) [IsDiscreteRep A] : ℚ :=
  ∏ q ∈ Finset.range 3, (Nat.card (cohomology A q) : ℚ) ^ ((-1 : ℤ) ^ q)

end GroundTheory.ProfCoh
