import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpenGlobal

theorem exists_unit (S : Scheme.{0}) (s : S) :
    ∃ n : ℕ, 2 ≤ n ∧ s ∈ S.basicOpen (n : Γ(S, ⊤)) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (R := S.presheaf.stalk s) (a := (3 : S.presheaf.stalk s)) (b := -2)
      (by norm_num) with h | h
  · refine ⟨3, by norm_num, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast h
  · refine ⟨2, le_rfl, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast (IsUnit.neg_iff _).1 h

theorem isOpen_connectedComponent_of_noetherian {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  rw [← isClosed_compl_iff, show (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z from
    Set.ext fun y => ⟨fun h => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, fun k => h (k mem_irreducibleComponent)⟩
      mem_irreducibleComponent, fun h k => by
      obtain ⟨Z, ⟨a, b⟩, c⟩ := Set.mem_iUnion₂.1 h
      exact b ((a.1.isConnected.isPreconnected.subset_connectedComponent c).trans (connectedComponent_eq k).ge)⟩]
  exact (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion fun Z h =>
    isClosed_of_mem_irreducibleComponents Z h.1

theorem exists_connected_open {S : Scheme.{0}} [IsLocallyNoetherian S] (N : S.Opens) (s : S) (hs : s ∈ N) :
    ∃ (V : Scheme.{0}) (w : V ⟶ S), IsOpenImmersion w ∧ ConnectedSpace V ∧ s ∈ Set.range w ∧
      Set.range w ⊆ (N : Set S) := by
  obtain ⟨U, hU, hsU, hUN⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := N) (x := s) hs
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace U.toScheme := inferInstance
  let V : U.toScheme.Opens := ⟨_, isOpen_connectedComponent_of_noetherian (X := U.toScheme) ⟨s, hsU⟩⟩
  have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, this, ⟨⟨⟨s, hsU⟩, mem_connectedComponent⟩, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hUN (V.ι v).2

theorem isOpen_abLocus_of_locallyNoetherian {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨n, h2, hn⟩ := exists_unit S s
  obtain ⟨V, w, hw, hV, ⟨v, rfl⟩, hle⟩ := exists_connected_open _ s hn
  have hG' : IsSemiAbelian ((Over.pullback w).obj G) := IsSemiAbelian.pullback w G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback w).obj G).left := GeometricallyConnected.connectedSpace ((Over.pullback w).obj G).hom ((Over.pullback w).obj G).hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty ((Over.pullback w).obj G).left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected ((Over.pullback w).obj G).hom x₀
  have hu : IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
    have h₀ := RingedSpace.isUnit_res_basicOpen S.toRingedSpace ((n : ℕ) : Γ(S, ⊤))
    have h₁ : (⊤ : V.Opens) ≤ w ⁻¹ᵁ S.basicOpen ((n : ℕ) : Γ(S, ⊤)) := fun y _ => hle ⟨y, rfl⟩
    have h₀' : IsUnit ((n : ℕ) : Γ(S, S.basicOpen ((n : ℕ) : Γ(S, ⊤)))) := by
      simp only [map_natCast] at h₀
      exact h₀
    have := h₀'.map (w.appLE _ ⊤ h₁).hom
    rwa [map_natCast] at this
  have hU := AbLocusOpen.isOpen_abLocus ((Over.pullback w).obj G) hG' hg h2 hu
  have key : ∀ y : V, w y ∈ abLocus G ↔ y ∈ abLocus ((Over.pullback w).obj G) := fun y =>
    abLocus_pullback abLocusOne hG (isGrpPullback_pullback G w).1 y
  refine ⟨w '' abLocus ((Over.pullback w).obj G), ?_, w.isOpenEmbedding.isOpenMap _ hU, ⟨v, (key v).1 hs, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (key y).2 hy

end GlobalTheory.AbLocusOpenGlobal

theorem GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_gmod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c), IsOpen (abLocus Z.t.G) := by
  intro E _ _ _ H D l Xo c Z
  have : IsLocallyNoetherian Z.X := (GlobalTheory.ModelRelCompare.densePart Z (GlobalTheory.CoeffRings.coeff_isDedFrac E H l c).1).1
  exact GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian Z.t.G Z.t.semi
