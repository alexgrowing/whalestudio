import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory groupCohomology

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H] [TopologicalSpace G]
  [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]

instance isDiscreteRep_tensorUnit : IsDiscreteRep (𝟙_ (Rep.{u} k G)) :=
  ⟨fun a => by
    have : stabilizer (𝟙_ (Rep.{u} k G)).ρ a = ⊤ := by
      ext g
      simp [mem_stabilizer]
    rw [this]
    exact isOpen_univ⟩

variable {A : Rep.{u} k G} [IsDiscreteRep A] {p : ℕ}

omit [IsTopologicalGroup H] in

theorem cocycles_ext {x y : cocycles A p}
    (h : cochainOf A (cocycleι A p x) = cochainOf A (cocycleι A p y)) : x = y :=
  cocycleι_injective (cochainOf_injective h)

omit [IsTopologicalGroup H] in

@[elab_as_elim]
theorem cohomology_induction_on {C : cohomology A p → Prop} (z : cohomology A p)
    (h : ∀ x : cocycles A p, C (cohomologyπ A p x)) : C z := by
  obtain ⟨x, rfl⟩ := cohomologyπ_surjective A p z
  exact h x

section Map

variable {B : Rep.{u} k G} [IsDiscreteRep B]

omit [IsTopologicalGroup H] in

theorem cochainOf_cocycleι_cyclesMap (f : A ⟶ B) (x : cocycles A p) :
    cochainOf B (cocycleι B p (HomologicalComplex.cyclesMap (cochainsMap f) p x)) =
      fun g => f.hom (cochainOf A (cocycleι A p x) g) :=
  congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (cochainsMap f) p)

omit [IsTopologicalGroup H] in

theorem cohomologyMap_cohomologyπ (f : A ⟶ B) (x : cocycles A p) :
    cohomologyMap f p (cohomologyπ A p x) =
      cohomologyπ B p (HomologicalComplex.cyclesMap (cochainsMap f) p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap f p) x

end Map

section MapAlong

variable {B : Rep.{u} k H} [IsDiscreteRep B] (φ : H →* G) (hφ : Continuous φ)
  (f : Rep.res φ A ⟶ B)

theorem cochainOf_cocycleι_cocyclesMapAlong (x : cocycles A p) :
    cochainOf B (cocycleι B p (cocyclesMapAlong φ hφ f p x)) =
      fun h => f.hom (cochainOf A (cocycleι A p x) (⇑φ ∘ h)) :=
  congrArg (fun ψ => cochainOf B (ψ.hom x))
    (HomologicalComplex.cyclesMap_i (cochainsMapAlong φ hφ f) p)

theorem cohomologyMapAlong_cohomologyπ (x : cocycles A p) :
    cohomologyMapAlong φ hφ f p (cohomologyπ A p x) =
      cohomologyπ B p (cocyclesMapAlong φ hφ f p x) :=
  ConcreteCategory.congr_hom (cohomologyπ_cohomologyMapAlong φ hφ f p) x

end MapAlong

end GroundTheory.ProfCoh
