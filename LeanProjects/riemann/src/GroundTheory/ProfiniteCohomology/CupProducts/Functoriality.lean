import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

theorem partialProd_comp_monoidHom {M N : Type*} [Monoid M] [Monoid N] {m : ℕ} (φ : M →* N)
    (x : Fin m → M) (j : Fin (m + 1)) :
    Fin.partialProd (⇑φ ∘ x) j = φ (Fin.partialProd x j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]
    rfl

section Tensor

variable (φ : H →* G)

def resTensorHom {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (f : Rep.res φ A ⟶ A')
    (g : Rep.res φ B ⟶ B') : Rep.res φ (A ⊗ B) ⟶ A' ⊗ B' :=
  (f ⊗ₘ g : Rep.res φ A ⊗ Rep.res φ B ⟶ A' ⊗ B')

@[simp]
theorem resTensorHom_tmul {A B : Rep.{u} k G} {A' B' : Rep.{u} k H} (f : Rep.res φ A ⟶ A')
    (g : Rep.res φ B ⟶ B') (a : A) (b : B) :
    (resTensorHom φ f g).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = f.hom a ⊗ₜ[k] g.hom b :=
  rfl

def resTensorIso (A B : Rep.{u} k G) : Rep.res φ (A ⊗ B) ≅ Rep.res φ A ⊗ Rep.res φ B :=
  Iso.refl (Rep.res φ A ⊗ Rep.res φ B)

@[simp]
theorem resTensorIso_hom_tmul (A B : Rep.{u} k G) (a : A) (b : B) :
    (resTensorIso φ A B).hom.hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) =
      (a ⊗ₜ[k] b : (Rep.res φ A ⊗ Rep.res φ B : Rep k H)) :=
  rfl

end Tensor

variable [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

section Naturality

variable {A A' B B' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A'] [IsDiscreteRep B]
  [IsDiscreteRep B'] {p q n : ℕ}

omit [TopologicalSpace H] [IsTopologicalGroup H] in

theorem cohomologyMap_tensorHom_cup (f : A ⟶ A') (g : B ⟶ B') (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap (f ⊗ₘ g) n (cup h x y) = cup h (cohomologyMap f p x) (cohomologyMap g q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cup_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMap_cohomologyπ,
    cohomologyMap_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cocycleι_cupCocycles,
    cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant, cochainOf_cocycleι_cyclesMap,
    cochainOf_cocycleι_cyclesMap]
  funext s
  exact tensorHom_cupCochain f g h _ _ s

omit [TopologicalSpace H] [IsTopologicalGroup H] in

theorem cohomologyMap_whiskerRight_cup (f : A ⟶ A') (h : p + q = n) (x : cohomology A p)
    (y : cohomology B q) :
    cohomologyMap (f ▷ B) n (cup h x y) = cup h (cohomologyMap f p x) y := by
  have := cohomologyMap_tensorHom_cup f (𝟙 B) h x y
  rwa [cohomologyMap_id, tensorHom_id] at this

end Naturality

section MapAlong

variable (φ : H →* G) (hφ : Continuous φ) {A B : Rep.{u} k G} {A' B' : Rep.{u} k H}
  [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep A'] [IsDiscreteRep B'] {p q n : ℕ}

theorem cohomologyMapAlong_resTensorHom_cup (f : Rep.res φ A ⟶ A') (g : Rep.res φ B ⟶ B')
    (h : p + q = n) (x : cohomology A p) (y : cohomology B q) :
    cohomologyMapAlong φ hφ (resTensorHom φ f g) n (cup h x y) =
      cup h (cohomologyMapAlong φ hφ f p x) (cohomologyMapAlong φ hφ g q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cup_cohomologyπ, cohomologyMapAlong_cohomologyπ, cohomologyMapAlong_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cocyclesMapAlong, cocycleι_cupCocycles, cocycleι_cupCocycles,
    cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
  funext s
  rw [cupCochain_apply, cupCochain_apply, resTensorHom_tmul, partialProd_comp_monoidHom]
  exact congrArg (TensorProduct.tmul k _) (Rep.hom_comm_apply g _ _)

end MapAlong

section Restriction

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

theorem cohomologyMap_resTensorIso_cohomologyRes_cup (S : Subgroup G) (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap (resTensorIso S.subtype A B).hom n (cohomologyRes (A ⊗ B) S n (cup h x y)) =
      cup h (cohomologyRes A S p x) (cohomologyRes B S q y) := by
  induction x using cohomology_induction_on with | h x => ?_
  induction y using cohomology_induction_on with | h y => ?_
  rw [cohomologyRes_eq, cohomologyRes_eq, cohomologyRes_eq, cup_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cohomologyMap_cohomologyπ, cohomologyMapAlong_cohomologyπ,
    cohomologyMapAlong_cohomologyπ, cup_cohomologyπ]
  congr 1
  apply cocycles_ext
  rw [cochainOf_cocycleι_cyclesMap, cochainOf_cocycleι_cocyclesMapAlong, cocycleι_cupCocycles,
    cocycleι_cupCocycles, cochainOf_cupLocallyConstant, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cocyclesMapAlong, cochainOf_cocycleι_cocyclesMapAlong]
  funext s
  simp only [cupCochain_apply]
  rw [partialProd_comp_monoidHom]
  rfl

end Restriction

section Inflation

variable (A B : Rep.{u} k G) (N : Subgroup G) [N.Normal]

def invariantsTensorLinearMap :
    (A.quotientToInvariants N ⊗ B.quotientToInvariants N : Rep k (G ⧸ N)) →ₗ[k]
      (A ⊗ B).quotientToInvariants N :=
  (TensorProduct.map (Submodule.subtype _) (Submodule.subtype _)).codRestrict _ fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      intro s
      exact congrArg₂ (TensorProduct.tmul k) (a.2 s) (b.2 s)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem coe_invariantsTensorLinearMap_tmul (a : A.quotientToInvariants N)
    (b : B.quotientToInvariants N) :
    (invariantsTensorLinearMap A B N (a ⊗ₜ[k] b) : (A ⊗ B : Rep k G)) =
      ((a : A) ⊗ₜ[k] (b : B) : (A ⊗ B : Rep k G)) :=
  rfl

def invariantsTensorHom :
    A.quotientToInvariants N ⊗ B.quotientToInvariants N ⟶ (A ⊗ B).quotientToInvariants N :=
  Rep.ofHom ⟨invariantsTensorLinearMap A B N, fun g => by
    induction g using QuotientGroup.induction_on with | H g => ?_
    apply TensorProduct.ext'
    intro a b
    exact Subtype.ext rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem invariantsTensorHom_tmul (a : A.quotientToInvariants N) (b : B.quotientToInvariants N) :
    ((invariantsTensorHom A B N).hom (a ⊗ₜ[k] b) : (A ⊗ B : Rep k G)) =
      ((a : A) ⊗ₜ[k] (b : B) : (A ⊗ B : Rep k G)) :=
  rfl

variable {A B} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

instance isDiscreteRep_quotientToInvariants_tensor :
    IsDiscreteRep ((A ⊗ B).quotientToInvariants N) :=
  isDiscreteRep_quotientToInvariants_of_normal (A ⊗ B) N

end Inflation

end GroundTheory.ProfCoh
