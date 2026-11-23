import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGenericFibreClosurePartitionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem separated_of_isOpen_component_subtype {X : Type*} [TopologicalSpace X] (F : Set X) (a : X)
    (ha : a ∈ F) (ho : IsOpen (connectedComponent (⟨a, ha⟩ : F))) :
    Disjoint (connectedComponentIn F a) (closure (F \ connectedComponentIn F a)) ∧
      Disjoint (closure (connectedComponentIn F a)) (F \ connectedComponentIn F a) := by
  have hC : connectedComponentIn F a = Subtype.val '' connectedComponent (⟨a, ha⟩ : F) :=
    connectedComponentIn_eq_image ha
  have hmem : ∀ y : F, (y : X) ∈ connectedComponentIn F a ↔ y ∈ connectedComponent (⟨a, ha⟩ : F) := by
    intro y
    rw [hC]
    exact Subtype.val_injective.mem_set_image
  obtain ⟨U, hU, hUe⟩ := isOpen_induced_iff.1 ho
  obtain ⟨Z, hZ, hZe⟩ := isClosed_induced_iff.1
    (isClosed_connectedComponent : IsClosed (connectedComponent (⟨a, ha⟩ : F)))
  constructor
  · have h1 : closure (F \ connectedComponentIn F a) ⊆ Uᶜ := by
      refine closure_minimal ?_ hU.isClosed_compl
      rintro y ⟨hyF, hy⟩ hyU
      apply hy
      refine (hmem ⟨y, hyF⟩).2 ?_
      rw [← hUe]
      exact hyU
    refine Set.disjoint_left.2 fun y hy hy' => h1 hy' ?_
    have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
    rw [← hUe] at this
    exact this
  · have h1 : closure (connectedComponentIn F a) ⊆ Z := by
      refine closure_minimal ?_ hZ
      intro y hy
      have := (hmem ⟨y, connectedComponentIn_subset F a hy⟩).1 hy
      rw [← hZe] at this
      exact this
    refine Set.disjoint_left.2 fun y hy hy' => hy'.2 ?_
    refine (hmem ⟨y, hy'.1⟩).2 ?_
    rw [← hZe]
    exact h1 hy

theorem isOpen_component_fibre_subtype {X S : Scheme.{0}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (a : (f ⁻¹' {s} : Set X)) : IsOpen (connectedComponent a) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))
  have hn : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have ho := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' _ hn ((f.fiberHomeo s).symm a)
  have h := (f.fiberHomeo s).isOpenMap _ ho
  have h2 : (f.fiberHomeo s) '' connectedComponent ((f.fiberHomeo s).symm a)
      = connectedComponent a := by
    have := (f.fiberHomeo s).image_connectedComponentIn (s := Set.univ)
      (x := (f.fiberHomeo s).symm a) (Set.mem_univ _)
    simpa [connectedComponentIn_univ, (f.fiberHomeo s).surjective.range_eq] using this
  rwa [h2] at h

theorem section_mem_component_generic_of_closed :
    ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (e σ : Spec (CommRingCat.of V) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → σ ≫ f = 𝟙 _ → σ (IsLocalRing.closedPoint V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} → σ (⊥ : PrimeSpectrum V) ∈ {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  intro V _ _ _ X f e σ hf he hσ hm
  have hfe : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (e p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  have hfσ : ∀ p : (Spec (CommRingCat.of V) : Scheme.{0}), f (σ p) = p := fun p => by
    rw [← Scheme.Hom.comp_apply, hσ]; rfl
  let g₀ : (Spec (CommRingCat.of V) : Scheme.{0}) := (⊥ : PrimeSpectrum V)
  let m : (Spec (CommRingCat.of V) : Scheme.{0}) := IsLocalRing.closedPoint V
  change σ m ∈ connectedComponentIn (f ⁻¹' {f (σ m)}) (e (f (σ m))) at hm
  change σ g₀ ∈ connectedComponentIn (f ⁻¹' {f (σ g₀)}) (e (f (σ g₀)))
  rw [hfσ] at hm ⊢
  have hsp : g₀ ⤳ m := IsLocalRing.specializes_closedPoint (R := V) ⊥
  have ha : e g₀ ∈ f ⁻¹' {g₀} := hfe g₀
  obtain ⟨h1, h2⟩ := separated_of_isOpen_component_subtype (f ⁻¹' {g₀}) (e g₀) ha
    (isOpen_component_fibre_subtype f g₀ ⟨e g₀, ha⟩)
  obtain ⟨hd, hu⟩ := GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition V X f hf (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
    (Set.union_diff_cancel (connectedComponentIn_subset _ _)) h1 h2
  by_contra hne
  have hσ' : σ m ∈ closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map σ.continuous).mem_closed isClosed_closure (subset_closure ⟨hfσ g₀, hne⟩)
  have he' : e m ∈ closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀)) :=
    (hsp.map e.continuous).mem_closed isClosed_closure
      (subset_closure (mem_connectedComponentIn ha))
  have hclopen : IsClopen (closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))) := by
    refine ⟨isClosed_closure, ?_⟩
    have : closure (connectedComponentIn (f ⁻¹' {g₀}) (e g₀))
        = (closure (f ⁻¹' {g₀} \ connectedComponentIn (f ⁻¹' {g₀}) (e g₀)))ᶜ :=
      (IsCompl.eq_compl ⟨hd, codisjoint_iff.2 hu⟩)
    rw [this]
    exact isClosed_closure.isOpen_compl
  have hsub := (isPreconnected_connectedComponentIn (x := e m) (F := f ⁻¹' {m})).subset_isClopen
    hclopen ⟨e m, mem_connectedComponentIn (hfe m), he'⟩
  exact Set.disjoint_left.1 hd (hsub hm) hσ'

end GlobalTheory
