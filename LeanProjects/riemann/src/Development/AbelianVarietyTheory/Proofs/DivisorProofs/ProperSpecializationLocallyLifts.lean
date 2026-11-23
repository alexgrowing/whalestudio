import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ImgSpec

theorem constructible_local {X : Type*} [TopologicalSpace X] {C : Set X}
    (hC : Topology.IsConstructible C) (x₀ : X) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      ((∀ z ∈ U, x₀ ⤳ z → z ∈ C) ∨ (∀ z ∈ U, x₀ ⤳ z → z ∉ C)) := by
  induction hC using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hUo _ =>
    by_cases hx₀ : x₀ ∈ U
    · exact ⟨U, hUo, hx₀, Or.inl fun z hz _ => hz⟩
    · exact ⟨Set.univ, isOpen_univ, trivial, Or.inr fun z _ hs hz => hx₀ (hs.mem_open hUo hz)⟩
  | union s _ t _ hs ht =>
    obtain ⟨U₁, o₁, m₁, h₁⟩ := hs
    obtain ⟨U₂, o₂, m₂, h₂⟩ := ht
    refine ⟨U₁ ∩ U₂, o₁.inter o₂, ⟨m₁, m₂⟩, ?_⟩
    rcases h₁ with h₁ | h₁
    · exact Or.inl fun z hz hs => Or.inl (h₁ z hz.1 hs)
    rcases h₂ with h₂ | h₂
    · exact Or.inl fun z hz hs => Or.inr (h₂ z hz.2 hs)
    · exact Or.inr fun z hz hs hm => hm.elim (h₁ z hz.1 hs) (h₂ z hz.2 hs)
  | compl s _ hs =>
    obtain ⟨U, o, m, h⟩ := hs
    exact ⟨U, o, m, h.symm.imp (fun h z hz hs => h z hz hs) (fun h z hz hs hm => hm (h z hz hs))⟩

end GlobalTheory.ImgSpec

open GlobalTheory.ImgSpec in

theorem GlobalTheory.image_contains_specializations_near : ∀ (F : Type) [Field F] [NumberField F] (Y : Scheme.{0}) (p : Y ⟶ Sp F), IsProper p → ∀ (V : Scheme.{0}) (π : V ⟶ Y), LocallyOfFiniteType π → ∀ ν : V, ∃ U : Y.Opens, π ν ∈ U ∧ ∀ z : Y, z ∈ U → π ν ⤳ z → ∃ u : V, π u = z := by
  intro F _ _ Y p hp V π hπ ν
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian Y := {}
  let g := V.affineCover.f (V.affineCover.idx ν)
  obtain ⟨w₀, hw₀⟩ := V.affineCover.covers ν
  let f := g ≫ π
  have : QuasiCompact f := inferInstance
  have : LocallyOfFinitePresentation f := inferInstance
  have hC := f.isConstructible_image (s := Set.univ) Topology.IsConstructible.univ
  obtain ⟨U, hUo, hx₀U, h⟩ := constructible_local hC (π ν)
  have hx₀ : π ν ∈ f '' Set.univ := ⟨w₀, trivial, by simp [f, g, hw₀]⟩
  rcases h with h | h
  · refine ⟨⟨U, hUo⟩, hx₀U, fun z hz hs => ?_⟩
    obtain ⟨w, -, rfl⟩ := h z hz hs
    exact ⟨g w, by simp [f]⟩
  · exact absurd hx₀ (h _ hx₀U (specializes_refl _))
