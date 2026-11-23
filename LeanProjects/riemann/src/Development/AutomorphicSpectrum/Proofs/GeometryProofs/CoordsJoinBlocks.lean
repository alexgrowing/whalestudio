import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZarhinBundleKernelFirstCoordEquations
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsCoordTieStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.AddBlockMulti

open GlobalTheory.CompanionTheory.Ar.ProjCoord

section Reindex

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem inChart_comp_equiv (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ κ' : Type} (e : κ' ≃ κ) (x : κ → Ω) (c : κ')
    (p : Cpt ξ) : InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
  unfold InChart
  refine and_congr Iff.rfl ⟨fun h c' => ?_, fun h c' => h _⟩
  simpa using h (e.symm c')

theorem coordTie_comp_equiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ κ' : Type}
    (e : κ' ≃ κ) {x : κ → Ω} (h : CoordTie o ξ x) : CoordTie o ξ (x ∘ e) := by
  have hr : ∀ c : κ', (Set.range fun j => (x ∘ e) j / (x ∘ e) c) = Set.range fun j => x j / x (e c) := fun c =>
    e.surjective.range_comp (fun j => x j / x (e c))
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (inChart_comp_equiv ξ e x _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    refine ⟨U, hU, fun q => ?_⟩
    rw [hq q]
    exact exists_congr fun hh => (inChart_comp_equiv ξ e x c ⟨q, hh⟩).symm
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (inChart_comp_equiv ξ e x c p).symm Iff.rfl

end Reindex

section OpenImm

variable {X Y : Scheme.{0}} {Ω : Type} [Field Ω]
variable (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) [IsOpenImmersion f]

theorem specializes_of_openImm {y : Y} (h : genPt (ζ ≫ f) ⤳ f y) : genPt ζ ⤳ y := by
  have e2 : genPt (ζ ≫ f) = f (genPt ζ) := Scheme.Hom.comp_apply _ _ _
  rw [e2] at h
  exact f.isOpenEmbedding.isInducing.specializes_iff.1 h

theorem inChart_push {κ : Type} (x : κ → Ω) (c : κ) (p : Cpt ζ) :
    InChart (ζ ≫ f) x c (push ζ f p) ↔ InChart ζ x c p := by
  unfold InChart
  rw [regAt_push]

variable {ζ f}

theorem exists_push (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (q : Cpt (ζ ≫ f)) :
    ∃ p : Cpt ζ, push ζ f p = q := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨y, rfl⟩ := hR q hq
  exact ⟨⟨y, specializes_of_openImm ζ f hq⟩, rfl⟩

theorem coordTie_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o ζ x) : CoordTie o (ζ ≫ f) x := by
  refine ⟨⟨?_, fun q => ?_⟩, fun q => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · rw [Scheme.stalkClosedPointTo_comp ζ f]
    have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    exact h.gen.bij.comp hb
  · obtain ⟨p, rfl⟩ := exists_push hR q
    exact genMap_push_injective ζ f p (h.gen.inj p)
  · obtain ⟨p, rfl⟩ := exists_push hR q
    obtain ⟨c, hc⟩ := h.cover p
    exact ⟨c, (inChart_push ζ f x c p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    refine ⟨f ''ᵁ U, hU.image_of_isOpenImmersion f, fun q => ⟨?_, ?_⟩⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, h2⟩ := (hq y).1 hy
      exact ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨y, rfl⟩ := hR q h1
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨y, (hq y).2 ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩, rfl⟩
  · rw [h.ring c hc a]
    constructor
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this

theorem coordTie_of_push {o : Type} [CommRing o] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    (hR : ∀ q : X, genPt (ζ ≫ f) ⤳ q → q ∈ Set.range f) (h : CoordTie o (ζ ≫ f) x) : CoordTie o ζ x := by
  refine ⟨⟨?_, fun p => ?_⟩, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · have hb : Function.Bijective (f.stalkMap (ζ (IsLocalRing.closedPoint Ω))).hom :=
      ConcreteCategory.bijective_of_isIso _
    have h1 := h.gen.bij
    rw [Scheme.stalkClosedPointTo_comp ζ f] at h1
    exact (Function.Bijective.of_comp_iff _ hb).1 h1
  · have h1 := h.gen.inj (push ζ f p)
    rw [genMap_push] at h1
    have hb : Function.Bijective (f.stalkMap p.1).hom := ConcreteCategory.bijective_of_isIso _
    exact (Function.Injective.of_comp_iff' _ hb).1 h1
  · obtain ⟨c, hc⟩ := h.cover (push ζ f p)
    exact ⟨c, (inChart_push ζ f x c p).1 hc⟩
  · obtain ⟨U, hU, hq⟩ := h.affine c hc
    have hle : U ≤ f.opensRange := fun q hqU => hR q ((hq q).1 hqU).1
    refine ⟨f ⁻¹ᵁ U, ?_, fun y => ⟨fun hy => ?_, ?_⟩⟩
    · have e : f ''ᵁ (f ⁻¹ᵁ U) = U := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
        exact inf_eq_right.2 hle
      rw [← f.isAffineOpen_iff_of_isOpenImmersion, e]
      exact hU
    · obtain ⟨h1, h2⟩ := (hq (f y)).1 hy
      have h1' := specializes_of_openImm ζ f h1
      exact ⟨h1', (inChart_push ζ f x c ⟨y, h1'⟩).1 h2⟩
    · rintro ⟨h1, h2⟩
      exact (hq (f y)).2 ⟨(push ζ f ⟨y, h1⟩).2, (inChart_push ζ f x c ⟨y, h1⟩).2 h2⟩
  · rw [h.ring c hc a]
    constructor
    · intro H p hp
      have := H (push ζ f p) ((inChart_push ζ f x c p).2 hp)
      rwa [regAt_push] at this
    · intro H q hq
      obtain ⟨p, rfl⟩ := exists_push hR q
      rw [regAt_push]
      exact H p ((inChart_push ζ f x c p).1 hq)

end OpenImm

section Model

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem spec_int_hom_ext (g g' : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of ℤ)) : g = g' := by
  rw [← Spec.map_preimage g, ← Spec.map_preimage g']
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext_int _ _)

theorem exists_openModel {κ : Type} {x : κ → Ω} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) :
    ∃ (Y : Scheme.{0}) (ζ : Spec (CommRingCat.of Ω) ⟶ Y) (f : Y ⟶ X) (_ : IsOpenImmersion f), ζ ≫ f = ξ ∧
      (∀ q : X, genPt ξ ⤳ q → q ∈ Set.range f) ∧ ∀ q : Y, genPt ζ ⤳ q := by
  let W : X.Opens := sSup {U : X.Opens | ∀ q ∈ U, genPt ξ ⤳ q}
  have hW : ∀ q ∈ W, genPt ξ ⤳ q := by
    intro q hq
    obtain ⟨U, hU, hqU⟩ := TopologicalSpace.Opens.mem_sSup.1 hq
    exact hU q hqU
  have hC : ∀ q : X, genPt ξ ⤳ q → q ∈ W := by
    intro q hq
    obtain ⟨c, hc⟩ := h.cover ⟨q, hq⟩
    obtain ⟨U, -, hU⟩ := h.affine c hc.1
    refine TopologicalSpace.Opens.mem_sSup.2 ⟨U, fun r hr => ((hU r).1 hr).1, (hU q).2 ⟨hq, hc⟩⟩
  have hr : Set.range ξ ⊆ Set.range W.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    subst hz
    rw [Scheme.Opens.range_ι]
    exact hC _ specializes_rfl
  have e : IsOpenImmersion.lift W.ι ξ hr ≫ W.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  have hR : ∀ q : X, genPt ξ ⤳ q → q ∈ Set.range W.ι := fun q hq => by
    rw [Scheme.Opens.range_ι]
    exact hC q hq
  refine ⟨W, IsOpenImmersion.lift W.ι ξ hr, W.ι, inferInstance, e, hR, fun q => ?_⟩
  refine specializes_of_openImm _ W.ι ?_
  rw [e]
  exact hW _ q.2

theorem coordTie_join {κ κ' : Type} [Finite κ] [Finite κ'] {x : κ → Ω} {w : κ' → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (h : CoordTie ℤ ξ x) (hw : ∀ p : Cpt ξ, ∃ l, InChart ξ w l p) :
    CoordTie ℤ ξ (joinCo (RingHom.id Ω) x w) := by
  obtain ⟨Y, ζ, f, _, rfl, hR, hall⟩ := exists_openModel h
  let M : PModel ℤ x :=
    { X := Y
      ξ := ζ
      s := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom _))
      hover := spec_int_hom_ext _ _
      all := hall
      tie := coordTie_of_push hR h }
  refine coordTie_push hR (GlobalTheory.T.join_coords_coordTie ℤ Ω κ x M κ' w fun p => ?_)
  obtain ⟨l, hl⟩ := hw (push ζ f p)
  exact ⟨l, (inChart_push ζ f w l p).1 hl⟩

end Model

theorem add_block_multi : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type)
    [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K']
    (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω),
    CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) →
    CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k =>
      (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  intro X Ω _ ξ K _ J _ y K' _ J' _ s h hs
  have hw : ∀ p : Cpt ξ, ∃ i, InChart ξ (fun c : (k : K') → J' k => ∏ k, s ⟨k, c k⟩) i p := by
    intro p
    choose i hi using fun k => hs k p
    refine ⟨i, Finset.prod_ne_zero_iff.2 fun k _ => (hi k).1, fun c' => ?_⟩
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => (hi k).2 (c' k)
  have h2 := coordTie_join (κ := (k : K) → J k) (κ' := (k : K') → J' k) h hw
  exact coordTie_comp_equiv (Equiv.sumPiEquivProdPi (Sum.elim J J')) h2

end GlobalTheory.CompanionTheory.Ar.AddBlockMulti
